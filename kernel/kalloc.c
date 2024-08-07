// Physical memory allocator, for user processes,
// kernel stacks, page-table pages,
// and pipe buffers. Allocates whole 4096-byte pages.

#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "spinlock.h"
#include "riscv.h"
#include "defs.h"

void freerange(void *pa_start, void *pa_end);

extern char end[]; // first address after kernel.
                   // defined by kernel.ld.

struct run {
  struct run *next;
};

struct {
  struct spinlock lock;
  struct run *freelist;
} kmem;

// array to record page reference count
#define refsz ((PHYSTOP - KERNBASE)/PGSIZE)
int ref[refsz];

void
kinit()
{
  initlock(&kmem.lock, "kmem");
  memset(ref, 0, refsz * sizeof(int));
  freerange(end, (void*)PHYSTOP);
  //printf("start:[%p],end:[%p],total page:[%d],sz:[%d]\n", end, PHYSTOP, (PHYSTOP -  PGROUNDUP((uint64)end))/PGSIZE, refsz);
}

void
freerange(void *pa_start, void *pa_end)
{
  char *p;
  p = (char*)PGROUNDUP((uint64)pa_start);
  for(; p + PGSIZE <= (char*)pa_end; p += PGSIZE){
    ref[PGINDEX(p)] = 1;
    kfree(p);
  }
}

// Free the page of physical memory pointed at by v,
// which normally should have been returned by a
// call to kalloc().  (The exception is when
// initializing the allocator; see kinit above.)
void
kfree(void *pa)
{
  struct run *r;

  if(((uint64)pa % PGSIZE) != 0 || (char*)pa < end || (uint64)pa >= PHYSTOP)
    panic("kfree");

  ref[PGINDEX(pa)] -= 1;
  if(ref[PGINDEX(pa)] > 0){
    return;
  }
  //printf("free page ref:%d\n", ref[PGINDEX(pa)]);
  // Fill with junk to catch dangling refs.
  memset(pa, 1, PGSIZE);

  r = (struct run*)pa;

  acquire(&kmem.lock);
  r->next = kmem.freelist;
  kmem.freelist = r;
  release(&kmem.lock);
}

// Allocate one 4096-byte page of physical memory.
// Returns a pointer that the kernel can use.
// Returns 0 if the memory cannot be allocated.
void *
kalloc(void)
{
  struct run *r;

  acquire(&kmem.lock);
  r = kmem.freelist;
  if(r)
    kmem.freelist = r->next;
  
  release(&kmem.lock);

  if(r)
    memset((char*)r, 5, PGSIZE); // fill with junk

  if(r){
    uint64 pa = (uint64)r;
    //printf("kalloc index: [%d]\n", PGINDEX(pa));
    ref[PGINDEX(pa)] = 1;
  }
  return (void*)r;
}
