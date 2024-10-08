#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  int alloc_size = (raw_size + 15) & ~15;
  if (alloc_size == 0) {
	return NULL;
  }
  int total_size = alloc_size + sizeof(header) - 2 * sizeof(header *);
  int index = ((alloc_size) / 16) - 1;
  if (index > N_LISTS - 1) {
	index = N_LISTS - 1;
  }
  int i;
  header * cur;
  for (i = index; i < N_LISTS - 1; i++) {
  	if (freelistSentinels[i].next != &freelistSentinels[i]) {
		break;
	}
  }  
  if (i == N_LISTS - 1) {
  	cur = (freelistSentinels[i].next);
        while(cur != &freelistSentinels[i]) {
		if (get_size(cur) >= total_size) {
			break;
		}	
		cur = cur->next;	
        }
	if (cur == &freelistSentinels[i]) {
        	while(1) {
			header * newChunk = allocate_chunk(ARENA_SIZE);  
			if (lastFencePost == NULL || (header *)((char*)lastFencePost + (ALLOC_HEADER_SIZE)) != (header *)((char*)newChunk - ALLOC_HEADER_SIZE)) {
				int index = (ARENA_SIZE - 2 * ALLOC_HEADER_SIZE - sizeof(header) + 2 * sizeof(header *)) / 16 - 1;
			 	if (index > N_LISTS - 1) {
               				index = N_LISTS - 1;
       				}  
				newChunk->prev = freelistSentinels[index].prev;
				newChunk->next = &(freelistSentinels[index]);
				freelistSentinels[index].prev->next = newChunk;
				freelistSentinels[index].prev = newChunk;
				insert_os_chunk((char*)newChunk - ALLOC_HEADER_SIZE);
				lastFencePost = (header *)((char*)newChunk + get_size(newChunk));
			        if (get_size(newChunk) - sizeof(header) + 2 * sizeof(header *) >= total_size) {
					cur = newChunk;
					break;
				}	
			} else {
				
				int og_size = 0;
				header * start;
				if (get_state(get_left_header(lastFencePost)) == UNALLOCATED) {
					start = get_left_header(lastFencePost);
					og_size = get_size(start);
				} else {
					start = lastFencePost;
				}	
				//printf("%d %d", get_state(get_left_header(lastFencePost)), get_size(get_left_header(lastFencePost)));
				int index;			
				if (og_size) {
					index = (get_size(start) - sizeof(header) + 2 * sizeof(header *)) / 16 - 1;		
					set_size(start, get_size(start) + ARENA_SIZE);
					set_state(start, UNALLOCATED);
					lastFencePost = (header *)((char*)start + get_size(start));
					lastFencePost->left_size = get_size(start);
					if (index > N_LISTS - 1) {
						index = N_LISTS - 1;
					}
					header * current = freelistSentinels[index].next;
					while (current != &freelistSentinels[index]) {
						if (current == start) {
							current->prev->next = current->next;
							current->next->prev = current->prev;
							break;
						}				
						current = current->next;		
					}
					///insert coalesced into correct free list
					index = (get_size(start) - sizeof(header) + 2 * sizeof(header *)) / 16 - 1;
					if (index > N_LISTS - 1) {
						index = N_LISTS - 1;
					}
					        start->prev = freelistSentinels[index].prev;
                                		start->next = &(freelistSentinels[index]);
                                 		freelistSentinels[index].prev->next = start;
                                 		freelistSentinels[index].prev = start;
						 
				} else {
					index = (ARENA_SIZE - 1 * sizeof(header) + 2 * sizeof(header *)) / 16 - 1; 
					if (index > N_LISTS - 1) {
						index = N_LISTS - 1;
					}
					set_state(start, UNALLOCATED);
					set_size(start, ARENA_SIZE - sizeof(header) + sizeof(header));
					start->prev = freelistSentinels[index].prev;
					start->next = &(freelistSentinels[index]);
					freelistSentinels[index].prev->next = start;
					freelistSentinels[index].prev = start;	
					lastFencePost = (header *)((char *) start + get_size(start));
					lastFencePost->left_size = get_size(start);					
				}
				if (get_size(start) >= total_size) {
                		cur = start;
                		break;
                		}	
			}
			
		}
        }
  } else {
  	cur = freelistSentinels[i].next;
  }
  cur->prev->next = cur->next;
  cur->next->prev = cur->prev;  
  if (get_size(cur) - total_size  < sizeof(header)) {
	set_state(cur, ALLOCATED);
  	return (header *) cur->data;
  } else {
  	header * freeobj = get_header_from_offset(cur, total_size);
        set_size(freeobj, get_size(cur) - total_size);
	set_state(freeobj, UNALLOCATED);
	freeobj->left_size = total_size;
        header * right = get_right_header(freeobj);
	right->left_size = get_size(freeobj);
	int sliverIndex = ((get_size(freeobj) - sizeof(header) + (2 * sizeof(header *))) / 16) - 1;
	if (sliverIndex > N_LISTS - 1) {
		sliverIndex = N_LISTS - 1;
	}
	freeobj->prev = freelistSentinels[sliverIndex].prev;
	freeobj->next = &(freelistSentinels[sliverIndex]);
	freelistSentinels[sliverIndex].prev->next = freeobj;
	freelistSentinels[sliverIndex].prev = freeobj;
 	set_size_and_state(cur, total_size, ALLOCATED);
	return (header *) cur->data;       	         
  }
  
  (void) raw_size;
  assert(false);
  exit(1);
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  if (p == NULL) {
	return;	
  }
  header * hdr = (header *)((char*)p - sizeof(header) + 2 * sizeof(header *));
  if (get_state(hdr) != ALLOCATED) {
printf("Double Free Detected\n");
assert(false);
return;
  }
  int left_state = (get_state(get_left_header(hdr)) == FENCEPOST || get_state(get_left_header(hdr)) == ALLOCATED);
  int right_state = (get_state(get_right_header(hdr)) == FENCEPOST  || get_state(get_right_header(hdr)) == ALLOCATED);
  if (left_state == 1 && right_state == 1) {
  	set_state(hdr, UNALLOCATED);
	int index = (get_size(hdr) - sizeof(header) + 2 * sizeof(header *)) / 16 - 1;
	if (index > N_LISTS - 1) {
		index = N_LISTS - 1;
  	}
	
	hdr->prev = freelistSentinels[index].prev;
        hdr->next = &(freelistSentinels[index]);
        freelistSentinels[index].prev->next = hdr;
        freelistSentinels[index].prev = hdr;
	
  } else if (left_state == 0 && right_state == 1) {
	int index = (get_size((hdr)) - sizeof(header) + 2 * sizeof(header *)) / 16 - 1;
	if (index > N_LISTS - 1) {
		index = N_LISTS - 1;
	}
  	set_size(get_left_header(hdr), get_size(hdr) + get_size(get_left_header(hdr)));
	header * check = freelistSentinels[index].next;
	while (check != &freelistSentinels[index]) {
		if (check == get_left_header(hdr)) {
			check->prev->next = check->next;
			check->next->prev = check->prev;
			break;
		}
		check = check->next;
        }
	index = (get_size(get_left_header(hdr)) - sizeof(header) + 2 * sizeof(header *)) / 16 - 1;
	if (index > N_LISTS - 1) {
		index = N_LISTS - 1;
	}
	get_left_header(hdr)->prev = freelistSentinels[index].prev;
        get_left_header(hdr)->next = &(freelistSentinels[index]);
        freelistSentinels[index].prev->next = get_left_header(hdr);
        freelistSentinels[index].prev = get_left_header(hdr);
	get_right_header(get_left_header(hdr))->left_size = get_size(get_left_header(hdr));	
  } else if (left_state == 1 && right_state == 0) {
int index = ((get_size(get_right_header(hdr)) - sizeof(header) + 2 * sizeof(header *))) / 16 - 1;
if (index > N_LISTS - 1) {
	index = N_LISTS - 1;
}
header * m = get_right_header(hdr);
set_size((hdr), get_size(hdr) + get_size(get_right_header(hdr)));
set_state(hdr, UNALLOCATED);
header * check = freelistSentinels[index].next;
while (check != &freelistSentinels[index]) {
        if (check == m) {
                check->prev->next = check->next;
                check->next->prev = check->prev;
                break;
        }
	check = check->next;
}
index = (get_size((hdr)) + 2 * sizeof(header *) - sizeof(header)) / 16 - 1;
if (index > N_LISTS - 1) {
	index = N_LISTS - 1;
}
(hdr)->prev = freelistSentinels[index].prev;
(hdr)->next = &(freelistSentinels[index]);
freelistSentinels[index].prev->next = (hdr);
freelistSentinels[index].prev = (hdr);
get_right_header(hdr)->left_size = get_size(hdr);
  } else {
  	       int index1 = (get_size(hdr) - sizeof(header) + 2 * sizeof(header *)) / 16 - 1;
	 	int index2 = (get_size(get_left_header(hdr)) - sizeof(header) + 2 * sizeof(header *)) / 16 - 1;
		int index3 = (get_size(get_right_header(hdr)) - sizeof(header) + 2 * sizeof(header *)) / 16 - 1;
		if (index1 > N_LISTS - 1) {
			index1 = N_LISTS - 1;
		}
		if (index2 > N_LISTS - 1) {
			index2 = N_LISTS - 1;
		}
		if (index3 > N_LISTS - 1) {
			index3 = N_LISTS - 1;
		}
		set_size(get_left_header(hdr), get_size(get_left_header(hdr)) + get_size(get_right_header(hdr)) + get_size(hdr));
		header * check = freelistSentinels[index1].next;
while (check != &freelistSentinels[index1]) {
        if (check == (hdr)) {
                check->prev->next = check->next;
                check->next->prev = check->prev;
                break;
        }
	check = check->next;
}
check = freelistSentinels[index2].next;
while (check != &freelistSentinels[index2]) {
        if (check == get_left_header(hdr)) {
                check->prev->next = check->next;
                check->next->prev = check->prev;
                break;
        }
	check = check->next;
}
check = freelistSentinels[index3].next;
while (check != &freelistSentinels[index3]) {
        if (check == get_right_header(hdr)) {
                check->prev->next = check->next;
                check->next->prev = check->prev;
                break;
        }
	check - check->next;
}
	index1 = (get_size(get_left_header(hdr)) - sizeof(header) + 2 * sizeof(header *)) / 16 - 1;	
	if (index1 > N_LISTS - 1) {
        index1 = N_LISTS - 1;
}
get_left_header(hdr)->prev = freelistSentinels[index1].prev;
get_left_header(hdr)->next = &(freelistSentinels[index1]);
freelistSentinels[index1].prev->next = get_left_header(hdr);
freelistSentinels[index1].prev = get_left_header(hdr);
get_right_header(get_left_header(hdr))->left_size = get_size(get_left_header(hdr));
  }
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem;
 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
