#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "myMalloc.h"
#include "printing.h"

#define MALLOC_COLOR "MALLOC_DEBUG_COLOR"

static bool check_env;
static bool use_color;

/**
 * Print just the block's size
 */
void basic_print(header * block) {
	printf("[%zd] -> ", get_size(block));
}

/**
 * Print just the block's size
 */
void print_list(header * block) {
	printf("[%zd]\n", get_size(block));
}

/**
 * return a string representing the allocation status
 */
static inline const char * allocated_to_string(char allocated) {
  switch(allocated) {
    case UNALLOCATED: 
      return "false";
    case ALLOCATED:
      return "true";
    case FENCEPOST:
      return "fencepost";
  }
  assert(false);
}

static bool check_color() {
  if (!check_env) {
    // genenv allows accessing environment varibles
    const char * var = getenv(MALLOC_COLOR);
    use_color = var != NULL && !strcmp(var, "1337_CoLoRs");
    check_env = true;
  }
  return use_color;
}

/**
 * Change the tty color based on the block's allocation status
 */
static void print_color(header * block) {
  if (!check_color()) {
    return;
  }

  switch(get_state(block)) {
    case UNALLOCATED:
      printf("\033[0;32m");
      break;
    case ALLOCATED:
      printf("\033[0;34m");
      break;
    case FENCEPOST:
      printf("\033[0;33m");
      break;
  }
}

static void clear_color() {
  if (check_color()) {
    printf("\033[0;0m");
  }
}

static inline bool is_sentinel(void * p) {
  for (int i = 0; i < N_LISTS; i++) {
    if (&freelistSentinels[i] == p) {
      return true;
    }
  }
  return false;
}

/**
 * Print the free list pointers if RELATIVE_POINTERS is set to true
 * then print the pointers as an offset from the base of the heap. This allows
 * for determinism in testing. 
 */
void print_pointer(void * p) {
  if (is_sentinel(p)) {
    printf("SENTINEL");
  } else {
    if (RELATIVE_POINTERS) {
      printf("%04zd", p - base);
    } else {
      printf("%p", p);
    }
  }
}

/**
 * Verbose printing of all of the metadata fields of each block
 */
void print_object(header * block) {
  print_color(block);

  printf("[\n");
  printf("\taddr: ");
  print_pointer(block);
  puts("");
  printf("\tsize: %zd\n", get_size(block) );
  printf("\tleft_size: %zd\n", block->left_size);
  printf("\tallocated: %s\n", allocated_to_string(get_state(block)));
  if (!get_state(block)) {
    printf("\tprev: ");
    print_pointer(block->prev);
    puts("");

    printf("\tnext: ");
    print_pointer(block->next);
    puts("");
  }
  printf("]\n");

  clear_color();
}

/**
 * Simple printer that just prints the allocation status of each block
 */
void print_status(header * block) {
  print_color(block);
  switch(get_state(block)) {
    case UNALLOCATED:
      printf("[U]");
      break;
    case ALLOCATED:
      printf("[A]");
      break;
    case FENCEPOST:
      printf("[F]");
      break;
  }
  clear_color();
}

/*
static void print_bitmap() {
  printf("bitmap: [");
  for(int i = 0; i < N_LISTS; i++) {
    if ((freelist_bitmap[i >> 3] >> (i & 7)) & 1) {
      printf("\033[32m#\033[0m");
    } else {
      printf("\033[34m_\033[0m");
    }
    if (i % 8 == 7) {
      printf(" ");
    }
  }
  puts("]");
}
*/

/**
 * Print a linked list between two nodes using a provided print function
 */
void print_sublist(printFormatter pf, header * start, header * end) {  
  for (header * cur = start; cur != end; cur = cur->next) {
    pf(cur); 
  }
}

/**
 * print the full freelist
 */
void freelist_print(printFormatter pf) {
  if (!pf) {
    return;
  }

  for (size_t i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    if (freelist->next != freelist) {
      printf("L%zu: ", i);
      print_sublist(pf, freelist->next, freelist);
      puts("");
    }
    fflush(stdout);
  }
}

/**
 * print the boundary tags from each chunk from the OS
 */
void tags_print(printFormatter pf) {
  if (!pf) {
    return;
  }

  for (size_t i = 0; i < numOsChunks; i++) {
    header * chunk = osChunkList[i];
    pf(chunk);
    for (chunk = get_right_header(chunk);
         get_state(chunk) != FENCEPOST; 
         chunk = get_right_header(chunk)) {
        pf(chunk);
    }
    pf(chunk);
    fflush(stdout);
  }
}
