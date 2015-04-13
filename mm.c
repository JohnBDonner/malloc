/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "swagsauce",
    /* First member's full name */
    "John B. Donner",
    /* First member's email address */
    "jdonner4@u.rochester.edu",
    /* Second member's full name (leave blank if none) */
    "Lindsey E. Curtis",
    /* Second member's email address (leave blank if none) */
    "lcurtis2@u.rochester.edu"
};

/* 16 byte alignment */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT) -1) & ~(ALIGNMENT- 1))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Extend heap */
#define BLOCK_SIZE sizeof(struct s_block)

/* linkedlist structure */
typedef struct s_block *t_block;
struct s_block {
    size_t size;
    t_block next;
    int free;
};

/* helper methods */
inline t_block find_block(t_block *last, size_t size);

/* Global Variable */
void *base = NULL;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    t_block b, last;
    size_t s;
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);

    if (p == (void *)-1) {
	    return NULL;
    } else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing... for now.
 */
void mm_free(void *ptr) { }

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL) {
      return NULL;
    }

    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize) {
      copySize = size;
    }

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);

    return newptr;
}

t_block find_block (t_block *last, size_t size){
    t_block b = base;
    while (b && !(b->free && b->size >= size)) {
        *last = b;
        b = b->next;
    }
    return b;
}

t_block extend_heap (t_block last, size_t s){
    t_block b;
    b = sbrk (0);
    if (sbrk( BLOCK_SIZE + s) == (void*) -1) /* sbrk fails , go to die */
        return (NULL );
    b->size = s;
    b->next = NULL;
    if (last)
        last ->next = b;
    b->free = 0;
    return (b);
}


