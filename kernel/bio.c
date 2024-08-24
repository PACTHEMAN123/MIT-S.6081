// Buffer cache.
//
// The buffer cache is a linked list of buf structures holding
// cached copies of disk block contents.  Caching disk blocks
// in memory reduces the number of disk reads and also provides
// a synchronization point for disk blocks used by multiple processes.
//
// Interface:
// * To get a buffer for a particular disk block, call bread.
// * After changing buffer data, call bwrite to write it to disk.
// * When done with the buffer, call brelse.
// * Do not use the buffer after calling brelse.
// * Only one process at a time can use a buffer,
//     so do not keep them longer than necessary.


#include "types.h"
#include "param.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "riscv.h"
#include "defs.h"
#include "fs.h"
#include "buf.h"

#define NBUCKETS 13
struct {
  struct spinlock lock;
  struct buf buf[NBUF];

  // buf hashmap
  struct spinlock bklock[NBUCKETS];
  struct buf *buckets[NBUCKETS];
} bcache;

extern uint ticks;

void
binit(void)
{
  struct buf *b;

  initlock(&bcache.lock, "bcache");

  for(int i = 0; i < NBUCKETS; i++) {
    initlock(&bcache.bklock[i], "bcache.buckets");
    bcache.buckets[i] = 0;
  }
  for(b = bcache.buf; b < bcache.buf+NBUF; b++){
    // all add to bucket 0
    acquire(&bcache.bklock[0]);
    b->next = bcache.buckets[0];
    bcache.buckets[0] = b;
    release(&bcache.bklock[0]);
    initsleeplock(&b->lock, "buffer");
  }
}

// Look through buffer cache for block on device dev.
// If not found, allocate a buffer.
// In either case, return locked buffer.
static struct buf*
bget(uint dev, uint blockno)
{
  struct buf *b;

  //acquire(&bcache.lock);

  // Is the block already cached?
  int bkid = blockno % NBUCKETS;
  acquire(&bcache.bklock[bkid]);
  for(b = bcache.buckets[bkid]; b != 0; b = b->next) {
    //printf("b:[%p],[%d],head:[%p]\n", b, blockno, buckets[bkid].head);
    if(b->dev == dev && b->blockno == blockno){
      b->refcnt++;
      b->t = ticks;
      release(&bcache.bklock[bkid]);
      //release(&bcache.lock);
      acquiresleep(&b->lock);
      return b;
    }
  }
  release(&bcache.bklock[bkid]);

  // Not cached in the bucket.
  // Try to get a LRU buf from another bucket.
  acquire(&bcache.lock);
  struct buf *tb;
  uint ltime = 0xffffff;
  int find = 0;
  for(int i = 0; i < NBUCKETS; i++) {
    acquire(&bcache.bklock[i]);
    for(tb = bcache.buckets[i]; tb != 0; tb = tb->next) {
      if(tb->refcnt == 0) {
        // find a free buf
        find = 1;
        if(tb->t < ltime) {
          // update the LRU buf
          ltime = tb->t;
          b = tb;
        }
      }
    }
    release(&bcache.bklock[i]);
  }

  if(find) {
    // move the buf
    int bkid1 = b->blockno % NBUCKETS;
    // the eviction should be atomic to avoid deadlock
    if(bkid1 == bkid) {
      // special case
      acquire(&bcache.bklock[bkid]);
    } else {
      acquire(&bcache.bklock[bkid1]);
      acquire(&bcache.bklock[bkid]);
    }
    
    // remove from the original bucket.
    // search for the prev buf and modified its next.
    if(b == bcache.buckets[bkid1]) {
      // head
      bcache.buckets[bkid1] = b->next;
    } else {
      // not head
      for(tb = bcache.buckets[bkid1]; tb != 0; tb = tb->next) {
        if(tb->next == b) {
          tb->next = b->next;
          break;
        }
      }
    }
    
    // append to the new bucket
    b->next = bcache.buckets[bkid];
    bcache.buckets[bkid] = b;
    b->dev = dev;
    b->blockno = blockno;
    b->valid = 0;
    b->refcnt = 1;
    b->t = ticks;

    if(bkid == bkid1) {
      release(&bcache.bklock[bkid]);
    } else {
      release(&bcache.bklock[bkid]);
      release(&bcache.bklock[bkid1]);
    }
    
    
    //printf("ticks: %d\n", ticks);
    release(&bcache.lock);
    acquiresleep(&b->lock);
    return b;
  }

  panic("bget: no buffers");
}

// Return a locked buf with the contents of the indicated block.
struct buf*
bread(uint dev, uint blockno)
{
  struct buf *b;

  b = bget(dev, blockno);
  if(!b->valid) {
    virtio_disk_rw(b, 0);
    b->valid = 1;
  }
  return b;
}

// Write b's contents to disk.  Must be locked.
void
bwrite(struct buf *b)
{
  if(!holdingsleep(&b->lock))
    panic("bwrite");
  virtio_disk_rw(b, 1);
}

// Release a locked buffer.
// Move to the head of the most-recently-used list.
void
brelse(struct buf *b)
{
  if(!holdingsleep(&b->lock))
    panic("brelse");

  releasesleep(&b->lock);

  //acquire(&bcache.lock);
  b->refcnt--;
  //release(&bcache.lock);
}

void
bpin(struct buf *b) {
  acquire(&bcache.lock);
  b->refcnt++;
  release(&bcache.lock);
}

void
bunpin(struct buf *b) {
  acquire(&bcache.lock);
  b->refcnt--;
  release(&bcache.lock);
}


