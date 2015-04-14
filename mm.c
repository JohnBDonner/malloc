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

// Given at start
/* 16 byte alignment */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT) -1) & ~(ALIGNMENT- 1))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Extend heap */
#define BLOCK_SIZE sizeof(struct s_block)


#define NUM_FREELIST 10

// From Computer Systems (p. 830)
#define WSIZE     4       /* Word size in bytes */
#define DSIZE     16       /* Double word size in bytes */
#define CHUNKSIZE (1<<12) /* Page size in bytes */
#define MINSIZE   32      /* Minimum block size */

#define LISTS     20      /* Number of segregated lists */
#define BUFFER  (1<<7)    /* Reallocation buffer */

#define MAX(x, y) ((x) > (y) ? (x) : (y)) /* Maximum of two numbers */
#define MIN(x, y) ((x) < (y) ? (x) : (y)) /* Minimum of two numbers */

/* Pack size and allocation bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)            (*(unsigned int *)(p))
// Preserve reallocation bit
#define PUT(p, val)       (*(unsigned int *)(p) = (val) | GET_TAG(p)) // 2015-04-14-15:16 book doesn't have '| GET_TAG(p)'
// Clear reallocation bit
#define PUT_NOTAG(p, val) (*(unsigned int *)(p) = (val))

/* Store predecessor or successor pointer for free blocks */
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

/* Adjust the reallocation tag */
#define SET_TAG(p)   (*(unsigned int *)(p) = GET(p) | 0x2)
#define UNSET_TAG(p) (*(unsigned int *)(p) = GET(p) & ~0x2)

/* Read the size and allocation bit from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_TAG(p)   (GET(p) & 0x2)

/* Address of block's header and footer */
#define HEAD(ptr) ((char *)(ptr) - WSIZE)
#define FOOT(ptr) ((char *)(ptr) + GET_SIZE(HEAD(ptr)) - DSIZE)

/* Address of next and previous blocks */
#define NEXT(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))

// 1st implementation
/* Address of free block's predecessor and successor entries */
#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

/* Address of free block's predecessor and successor on the segregated list */
#define PRED(ptr) (*(char **)(ptr))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))

/* Settings for mm_check */
#define CHECK         1 /* Kill bit: Set to 0 to disable checking
                           (Checking is currently disabled through comments) */
#define CHECK_MALLOC  1 /* Check allocation operations */
#define CHECK_FREE    1 /* Check free operations */
#define CHECK_REALLOC 1 /* Check reallocation operations */
#define DISPLAY_BLOCK 1 /* Describe blocks in heap after each check */
#define DISPLAY_LIST  1 /* Describe free blocks in lists after each check */
#define PAUSE         1 /* Pause after each check, also enables the function to
                           skip displaying mm_check messages*/
                           
#define LINE_OFFSET   4 /* Line offset for referencing trace files */

/* Global Variable */
void *base = NULL;
static char *heap_listp;
void *free_lists[LISTS]; /* Array of pointers to segregated free lists */
char *prologue_block;    /* Pointer to prologue block */

/* Variables for checking function */
int line_count; // Running count of operations performed
int skip;       // Number of operations to skip displaying mm_check messages
                // (Checking still occurs)

/* linkedlist structure *//*
typedef struct s_block *t_block;
struct s_block {
    size_t size;
    t_block next;
    int free;
    char data[1];
};

/* helper methods */
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *coalesce(void *ptr);
static void place(void *ptr, size_t asize);

// Helper methods from 1st implementation
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);

static void mm_check(char caller, void *ptr, int size);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    // book implementation (p. 830)
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                             // Alignment Padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  // Prologue Header
    prologue_block = heap_listp + DSIZE;
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  // Prologue Footer
    PUT(heap_listp + (3 * WSIZE), PACK(DSIZE, 1));  // Epilogue Header

    line_count = LINE_OFFSET;
    skip = 0;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    // printf("extend EMPTY heap [%d]\n", CHUNKSIZE/WSIZE);
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * extend_heap - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
static void *extend_heap(size_t words) {
    char *ptr;
    size_t size;

    // printf("extending heap [%d]\n", words);
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    // printf("heapsize [%d]\n\n", size);
    if ((long)(ptr = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HEAD(ptr), PACK(size, 0)); // Free head block
    PUT(FOOT(ptr), PACK(size, 0)); // Free foot block
    PUT(HEAD(NEXT(ptr)), PACK(0, 1)); // New epilogue header

    /* Coalesce if the previous block was free */
    return coalesce(ptr);
}

/* 
 * mm_malloc - Performs a first-fit search of the implicit free list.m
 */
void *find_fit(size_t asize) {
    // dbg_printf("FINDING FIT: ");
    void *ptr;

    for (ptr = heap_listp; GET_SIZE(HEAD(ptr)) > 0; ptr = NEXT(ptr)) {
        if (!GET_ALLOC(HEAD(ptr)) && (asize <= GET_SIZE(HEAD(ptr)))) {
            return ptr;
        }
    }
    return NULL;

    /*
    void *bp;
    int class = getclass(asize);
    for (int i = class; i < NUM_FREELIST; i++) {
        void *root = getroot(i);
        // first fit search 
        for (bp = next_free_blck(root); bp != NULL; bp = next_free_blck(bp)) {
            dbg_printf(" %lx > ", (long)bp);
            if (asize <= GET_SIZE(HDRP(bp))) {
                dbg_printf("FOUND!\n");
                return bp;
            }
        }
    }
    
    // dbg_printf("NOT FOUND :(\n");
    return NULL; // no fit 
    */
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    //printf("Starting malloc with size [%d]........\n", size);
    int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *ptr = NULL;  /* Pointer */
    char *ptr; // Pointer
    void *p = mem_sbrk(newsize);
    size_t checksize = size; // Copy of request size (for use with mm_check)
    size_t asize, // adjusted block size
        extendsize; // amount to extend heap if no fit
    //printf("ptr start: %d\n", ptr);


    if (size <= 0)
        return NULL;

    
    // Adjust block size to include overhead and alignment reqs.
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
        // printf("2*dsize");
    } else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // Search the free list for a fit
    /*
    if ((ptr = find_fit(asize)) != NULL) {
        printf("findingfit...");
        place(ptr, asize);
        
        return ptr;
    }*/
    // asize = MAX(ALIGN(size + SIZE_T_SIZE), MINSIZE);

    // No fit found. Get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);
    if ((ptr = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(ptr, asize);
    // Checks
    line_count++;
    if (CHECK && CHECK_MALLOC) {
        mm_check('a', ptr, checksize);
    }
    return ptr;

    /* original implementation
    if (p == (void *)-1) {
        return NULL;
    } else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
    */
}

/*
 * place - place the requested block at the beginning of the free block,
 * splitting only if the size of the remainder would equal or exceed
 * the minimum block size.
 */
void place(void *ptr, size_t asize) {
    // printf("startingPLACE");
    size_t ptr_size = GET_SIZE(HEAD(ptr));
    size_t remainder = ptr_size - asize;

    // Remove block from segregated list 
    // delete_node(ptr);

    // printf("ptr=[[%d]]", ptr);
    // printf("NEXTptr=[[%d]]", NEXT(ptr));
    if (remainder >= MINSIZE) {
        PUT(HEAD(ptr), PACK(asize, 1));
        PUT(FOOT(ptr), PACK(asize, 1));
        ptr = NEXT(ptr);
        PUT(HEAD(ptr), PACK(remainder, 0));
        PUT(FOOT(ptr), PACK(remainder, 0));
    } else {
        PUT(HEAD(ptr), PACK(ptr_size, 1));
        PUT(FOOT(ptr), PACK(ptr_size, 1));
    }

    // splitting or not...
    /*
    if (remainder >= MINSIZE) {
        // Split block 
        PUT(HEAD(ptr), PACK(asize, 1)); // Block header
        PUT(FOOT(ptr), PACK(asize, 1)); // Block footer
        PUT_NOTAG(HEAD(NEXT(ptr)), PACK(remainder, 0)); // Next header
        PUT_NOTAG(FOOT(NEXT(ptr)), PACK(remainder, 0)); // Next footer
        insert_node(NEXT(ptr), remainder);
    } else {
        // Do not split block
        printf("don't split");
        PUT(HEAD(ptr), PACK(ptr_size, 1)); // Block header
        PUT(FOOT(ptr), PACK(ptr_size, 1)); // Block footer
    }
    */
    return;
}

/*
 * insert - for segragated list
 */
void insert_node(void *ptr, size_t size) {
    int list = 0;
    void *search_ptr = ptr;
    void *insert_ptr = NULL;

    // Select segregated list
    while ((list < LISTS - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    /* Select location on list to insert pointer while keeping list
     organized by byte size in ascending order. */
    search_ptr = free_lists[list];
    while ((search_ptr != NULL) && (size > GET_SIZE(HEAD(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = PRED(search_ptr);
    }

    // Set predecessor and successor 
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(ptr), search_ptr); 
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(PRED_PTR(ptr), search_ptr); 
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), NULL);

            // Add block to appropriate list
            free_lists[list] = ptr;
        }
    } else {
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), NULL);

            // Add block to appropriate list
            free_lists[list] = ptr;
        }
    }

    return;
}

/*
 * delete - for segragated list
 */
void delete_node(void *ptr) {
    int list = 0;
    size_t size = GET_SIZE(HEAD(ptr));

    // Select segregated list
    while ((list < LISTS - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    if (PRED(ptr) != NULL) {
        if (SUCC(ptr) != NULL) {
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
        } else {
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            free_lists[list] = PRED(ptr);
        }
    } else {
        if (SUCC(ptr) != NULL) {
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
        } else {
            free_lists[list] = NULL;
        }
    }

    return;
}

/*
 * mm_free - Freeing a block does nothing... for now.
 */
void mm_free(void *ptr) {
    size_t size = GET_SIZE(HEAD(ptr));

    PUT(HEAD(ptr), PACK(size, 0));
    PUT(FOOT(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * coalesce - used to merge a block with any adjacent free blocks in constant time.
 */
void *coalesce(void *ptr) {
    size_t prev_alloc = GET_ALLOC(FOOT(PREV(ptr)));
    size_t next_alloc = GET_ALLOC(HEAD(NEXT(ptr)));
    size_t size = GET_SIZE(HEAD(ptr));

    if (prev_alloc && next_alloc)               // case 1
        return ptr;
    else if (prev_alloc && !next_alloc) {       // case 2
        size += GET_SIZE(HEAD(NEXT(ptr)));
        PUT(HEAD(ptr), PACK(size, 0));
        PUT(FOOT(ptr), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {     // case 3
        size += GET_SIZE(HEAD(PREV(ptr)));
        PUT(FOOT(ptr), PACK(size, 0));
        PUT(FOOT(PREV(ptr)), PACK(size, 0));
        ptr = PREV(ptr);
    } else {                                    // case 4
        size += GET_SIZE(HEAD(PREV(ptr))) + GET_SIZE(FOOT(NEXT(ptr)));
        PUT(HEAD(PREV(ptr)), PACK(size, 0));
        PUT(FOOT(NEXT(ptr)), PACK(size, 0));
        ptr = PREV(ptr);
    }
    return ptr;
}

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

/*
 * mm_check - A heap checking method to help debug and check for consistency
 */
void mm_check(char caller, void* caller_ptr, int caller_size)
{
    int size;  // Size of block
    int alloc; // Allocation bit
    char *ptr = prologue_block + DSIZE;
    
    printf("ptr=(%d)\n", ptr);
    printf("HEAD(ptr)=(%d)\n", HEAD(ptr));
    printf("GET_SIZE(HEAD(ptr))=(%d)\n", GET_SIZE(HEAD(ptr)));
    int block_count = 1;
    int count_size;
    int count_list;
    int loc;   // Location of block relative to first block
    int caller_loc = (char *)caller_ptr - ptr;
    int list;
    char *scan_ptr;
    char skip_input;

    if (!skip) {
        printf("\n[%d] %c %d %d: Checking heap...\n", line_count, caller, caller_size, caller_loc);
    }

    while (1) {
        loc = ptr - prologue_block - DSIZE;

        size = GET_SIZE(HEAD(ptr));
        if (size == 0)
            break;

        alloc = GET_ALLOC(HEAD(ptr));

        // Print block information
        if (DISPLAY_BLOCK && !skip) {
            printf("%d: Block at location %d has size %d and allocation %d\n",
                block_count, loc, size, alloc);
            if (GET_TAG(HEAD(ptr))) {
                printf("%d: Block at location %d is tagged\n",
                    block_count, loc);
          }
        }

        // Check consistency of size and allocation in header and footer
        if (size != GET_SIZE(FOOT(ptr))) {
            printf("%d: Header size of %d does not match footer size of %d\n",
                block_count, size, GET_SIZE(FOOT(ptr)));
        }
        if (alloc != GET_ALLOC(FOOT(ptr))) {
            printf("%d: Header allocation of %d does not match footer allocation "
                "of %d\n", block_count, alloc, GET_ALLOC(FOOT(ptr)));
        }

        // Check if free block is in the appropriate list
        if (!alloc) {
            // Select segregated list
            list = 0;
            count_size = size;
            while ((list < LISTS - 1) && (count_size > 1)) {
                count_size >>= 1;
                list++;
            }

            // Check list for free block
            scan_ptr = free_lists[list];
            while ((scan_ptr != NULL) && (scan_ptr != ptr)) {
                scan_ptr = PRED(scan_ptr);
            }
            if (scan_ptr == NULL) {
                printf("%d: Free block of size %d is not in list index %d\n",
                    block_count, size, list);
            }
        }

        ptr = NEXT(ptr);
        block_count++;
    }

    if (!skip)
        printf("[%d] %c %d %d: Checking lists...\n",
            line_count, caller, caller_size, caller_loc);

    // Check every list of free blocks for validity
    for (list = 0; list < LISTS; list++) {
        ptr = free_lists[list];
        block_count = 1;

        while (ptr != NULL) {
            loc = ptr - prologue_block - DSIZE;
            size = GET_SIZE(HEAD(ptr));

            // Print free block information
            if (DISPLAY_LIST && !skip) {
                printf("%d %d: Free block at location %d has size %d\n",
                    list, block_count, loc, size);
                if (GET_TAG(HEAD(ptr))) {
                    printf("%d %d: Block at location %d is tagged\n",
                        list, block_count, loc);
                }
            }

            // Check if free block is in the appropriate list
            count_list = 0;
            count_size = size;

            while ((count_list < LISTS - 1) && (count_size > 1)) {
                count_size >>= 1;
                count_list++;
            }
            if (list != count_list) {
                printf("%d: Free block of size %d is in list %d instead of %d\n",
                    loc, size, list, count_list);
            }

            // Check validity of allocation bit in header and footer
            if (GET_ALLOC(HEAD(ptr)) != 0) {
                printf("%d: Free block has an invalid header allocation of %d\n",
                    loc, GET_ALLOC(FOOT(ptr)));
            }
            if (GET_ALLOC(FOOT(ptr)) != 0) {
                printf("%d: Free block has an invalid footer allocation of %d\n",
                    loc, GET_ALLOC(FOOT(ptr)));
            }

            ptr = PRED(ptr);
            block_count++;
        }
    }

    if (!skip)
        printf("[%d] %c %d %d: Finished check\n\n",
            line_count, caller, caller_size, caller_loc);

    // Pause and skip function, toggled by PAUSE preprocessor directive. Skip
    // allows checker to stop pausing and printing for a number of operations.
    // However, scans are still completed and errors will still be printed.
    if (PAUSE && !skip) {
        printf("Enter number of operations to skip or press <ENTER> to continue.\n");

        while ((skip_input = getchar()) != '\n') {
            if ((skip_input >= '0') && (skip_input <= '9')) {
                skip = skip * 10 + (skip_input - '0');
            }
        }

        if (skip)
            printf("Skipping %d operations...\n", skip);
        
    } else if (PAUSE && skip) {
        skip--;
    }

    return;
}

/*
void find_block() {
    
}

// Definitely need this method
void extend_heap() {

}

void split_block () {

}
*/

