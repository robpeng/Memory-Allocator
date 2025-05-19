#include <string.h>
#include <stdio.h>
#include <stdbool.h>

#include "myMalloc.h"
#include "testing.h"

/**
 * Print the name of the test file and the initial state of 
 *        the data structures
 */
void initialize_test(const char * name) {
  const char * filename = strrchr(name, '/');
  printf("TEST: %s\n", filename ? filename+1 : name);

  printf("INTIAL STATE\n\n");
  printf("FREELIST\n");
  freelist_print(print_object);
  printf("TAGS\n");
  tags_print(print_object);
}

/**
 * print the final state of the data structures and verify their 
 *        validity
 */
void finalize_test() {
  printf("FINAL STATE\n\n");

  printf("FREELIST\n");
  freelist_print(print_object);
  printf("TAGS\n");
  tags_print(print_object);
  verify();
}

/**
 * Allocate size byte of memory and zero the memory
 */
static void * malloc_and_clear(size_t size) {
  // Allocate memory
  void * mem = my_malloc(size);

  // Fill memory with 0 bytes
  memset(mem, 0, size);

  return mem;
}

/**
 * Malloc n allocations of size bytes
 */
void ** mallocing_loop(void ** array, size_t size, size_t n, printFormatter pf, bool silent) {
  if (!silent) {
    if (n == 1) {
      printf("mallocing %zu bytes\n", size);
    } else {
      printf("mallocing %zu bytes in %zu allocations\n", size, n);
    }
  }
  for (size_t i = 0; i < n; i++) {
    void * v = malloc_and_clear(size);
    if (array) {
      array[i] = v;
    }
  }
  if (!silent) {
    tags_print(pf);
    puts("");
  }
  verify();
  return array;
}

/**
 * Malloc only a single allocaion of size size
 */
void * mallocing(size_t size, printFormatter pf, bool silent) {
  void * p;
  return *mallocing_loop(&p, size, 1, pf, silent);
}

/**
 * check that the memory is still zeroed out and free it
 */
static void check_and_free(char * p, size_t size) {
  // Verify memory is still zeroed out from allocation
  for (size_t i = 0; i < size; i++) {
    if(p[i] != 0) {
      fprintf(stderr, "Memory Corruption Detected\n");
      break;
    }
  }

  // Free pointer
  my_free(p);
}

/**
 * Free an array of pointers returned by malloc
 */
void freeing_loop(void ** array, size_t size, size_t n, printFormatter pf, bool silent) {
  if (!silent) {
    if (n == 1) {
      printf("freeing %zu bytes (", size);
      print_pointer((char *) *array - sizeof(header));
      puts(")");
    } else {
      printf("freeing %zu bytes from %zu allocations\n", size, n);
    }
  }
  for (size_t i = 0; i < n; i++) {
    check_and_free(array[i], size);
  }
  if (!silent) {
    tags_print(pf);
    puts("");
  }
  verify();
}

/**
 * Free a single pointer allocated by malloc
 */
void freeing(void * p, size_t size, printFormatter pf, bool silent) {
  freeing_loop(&p, size, 1, pf, silent);
}
