/*
 * mm.c - 명시적 가용리스트를 이용한 할당기 구현
 * 
 * 가용한 블록들끼리 연결할 수 있도록 Predecessor, Successor를 포함한 블록 포맷 사용하였습니다.
 * 명시적 가용리스트 사용하여 가용한 블록끼리 연결하는 리스트(free_listp)를 생성하였습니다.
 * 명시적 가용리스트에 가용한 블록들이 들어가는 순서는 Last In, First Out 방식을 이용하였습니다.
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
    "swjungle_4th_b_week6_team5",
    /* First member's full name */
    "Park",
    /* First member's email address */
    "hyung@",
    /* Second member's full name (leave blank if none) */
    "young",
    /* Second member's email address (leave blank if none) */
    "Jang@"};

/*
 * 상수와 매크로함수 선언
 */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 10)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc)) /*크기와 할당비트를 통해 해더와 풋터를 저장할 수 있는 값을 리턴*/

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7) // p가 가리키는 블록의 크기
#define GET_ALLOC(p) (GET(p) & 0x1) // p가 가리키는 블록의 할당여부를 알려주는 비트(헤더의 마지막 비트값)

#define HDRP(bp) ((char *)(bp)-WSIZE)                        // bp가 가리키는 블록의 헤더
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // bp가 가리키는 블록의 풋터

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 다음 블록 주소값
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // 이전 블록 주소값

#define PRED_FREEP(bp) (*(void **)(bp))         // 가용리스트 bp가 가리키는 블록 바로 다음에 들어온 블록 주소값
#define SUCC_FREEP(bp) (*(void **)(bp + WSIZE)) // 가용리스트 bp가 가리키는 블록 바로 이전에 들어온 블록 주소값

static char *heap_listp; // 힙을 가리키는 주소
static char *free_listp; // 가용리스트의 첫번째 주소를 저장

void remove_block(char *bp);
void put_free_block(char *bp);
void *coalesce(void *bp);
void *find_fit(size_t asize);
void place(void *bp, size_t asize);

/*
* coalesce - bp가 가리키는 블록이 할당 해제되었을 때, 인접한 가용블럭들을 찾아 연결하는 함수
*            (Case 1, 2, 3, 4)
*/
void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc) // case 1
  {
    put_free_block(bp);
    return bp;
  }
  else if (prev_alloc && !next_alloc) // case 2
  {
    remove_block(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  else if (!prev_alloc && next_alloc) // case 3
  {
    remove_block(PREV_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  else // !prev_alloc && !next_alloc : case 4
  {
    remove_block(NEXT_BLKP(bp));
    remove_block(PREV_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  put_free_block(bp);
  return;
}

/*
* extend_heap 새 가용 블록으로 힙 확장하기
*/
void *extend_heap(size_t words)
{
  size_t size;
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

  char *bp = mem_sbrk(size);
  if (bp == -1)
  {
    return NULL;
  }

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // Epilogue 변경

  coalesce(bp);

  return;
}

/* 
 * mm_init - 할당기 생성자. 최초 6개 워드크기의 리스트 할당 후, CHUNKSIZE 만큼 힙 사이즈 확장
             [미사용패딩] - [Prologue Header] - [Predecessor] - [Successor] - [Prologue Footer] - [Epilogue를] 포함한 블록포맷 사용
 */
int mm_init(void)
{
  heap_listp = mem_sbrk(6 * WSIZE);
  if (heap_listp == (void *)-1)
  {
    return -1;
  }

  PUT(heap_listp, 0);                                // 미사용 패딩
  PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1)); // Prologue 헤더
  PUT(heap_listp + (2 * WSIZE), NULL);               // 가용리스트 내 Predecessor
  PUT(heap_listp + (3 * WSIZE), NULL);               // 가용리스트 내 Successor
  PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1)); // Prologue 푸터
  PUT(heap_listp + (5 * WSIZE), PACK(0, 1));         // Epilogue 헤더

  free_listp = heap_listp + DSIZE; //가용리스트 첫번째

  if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
  {
    return -1;
  }
  return 0;
}

/**
 * find_fit - 명시적 가용 리스트내에서 asize 크기 요청에 대한 가용한 블록 찾기(First fit 사용)
*/
void *find_fit(size_t asize)
{
  void *bp = free_listp;
  for (bp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp))
  {
    if (asize <= GET_SIZE(HDRP(bp)))
    {
      return bp;
    }
  }
  return NULL;
}

/**
 * place - bp가 가리키는 블록에 asize의 크기만큼 할당
*/
void place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp)); // csize : 블록의 크기, asize : 할당 크기

  remove_block(bp); // bp가 가리키는 블록은 할당되기 때문에 가용리스트에서 해제
  if ((csize - asize) >= (2 * DSIZE)) // 블록 크기랑 할당요구 크기랑 차이가 4워드 이상 날 경우, 내부단편화 방지를 위한 자르기
  {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp); 
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));

    put_free_block(bp);
  }
  else
  {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}

/* 
 * mm_malloc - Heap내에서 해당 size 요청에 맞는 크기의 메모리 블록을 할당하고,
 *             해당 블록 가리키는 주소값 반환 
 */
void *mm_malloc(size_t size)
{
  size_t asize;
  size_t extendsize;
  char *bp;

  if (size == 0)
  {
    return NULL;
  }

  if (size <= DSIZE)
  {
    asize = 2 * DSIZE;
  }
  else
  {
    asize = DSIZE * ((size + (DSIZE)) / DSIZE);
  }

  if ((bp = find_fit(asize)) != NULL)
  {
    place(bp, asize);
    return bp;
  }

  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    return NULL;
  place(bp, asize);
  return bp;
}

/*
 * mm_free - 해당 ptr이 가리키는 블록 할당 해제
 */
void mm_free(void *ptr)
{
  size_t size = GET_SIZE(HDRP(ptr));

  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
  coalesce(ptr);
}

/**
 * remove_block - 명시적 가용 리스트에서 할당된 블록(bp가 가리키는) 제거
 */
void remove_block(char *bp)
{

  if (bp == free_listp)
  {
    PRED_FREEP(SUCC_FREEP(bp)) = NULL;
    free_listp = SUCC_FREEP(bp);
  }
  else
  {
    SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp);
    PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp);
  }
}

/*
* put_free_block - 새로 생성된 가용블럭을 가용리스트 맨 앞에 추가해주기(Last In, First Out 방식)
*/
void put_free_block(char *bp)
{
  PRED_FREEP(bp) = NULL;
  SUCC_FREEP(bp) = free_listp;
  PRED_FREEP(free_listp) = bp;

  free_listp = bp;
}

/*
 * mm_realloc - 해당 ptr이 가리키는 블록 주소를 가지고 새로운 크기의 메모리 할당
 *              기존에 ptr이 가리키는 블록안의 내용은 새륩게 할당된 newptr이 가리키는 블록에 복사
 */
void *mm_realloc(void *old_ptr, size_t size) //이미 할당된 포인터 변수, 바꾸고 싶은 크기
{
  void *new_ptr;
  size_t old_size;

  if (size == 0)
  {
    mm_free(old_ptr);
    return 0;
  }
  if (old_ptr == NULL)
  {
    return mm_malloc(size);
  }

  new_ptr = mm_malloc(size);
  if (!new_ptr)
  {
    return 0;
  }

  old_size = GET_SIZE(HDRP(old_ptr));
  if (size < old_size)
  {
    old_size = size;
  }
  memcpy(new_ptr, old_ptr, old_size);
  mm_free(old_ptr);

  return new_ptr;
}
