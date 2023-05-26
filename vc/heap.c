void swap(int *a, int *b) {
  /*@ With x y px0 py0
      Require
        a == px0 && b == py0 &&
        store_int(px0, x) * store_int(py0, y)
      Ensure
        store_int(px0, y) * store_int(py0, x)
   */
  int t;
  t = *a;
  *a = *b;
  *b = t; 
}

void up(int *a, int pos) {
  /*@ With Hl Maxsize size0 pos0 a0 
      Require 
        all_int(Hl) && 2 <= Maxsize && Maxsize <= INT_MAX &&
        1 <= pos0 && pos0 <= size0 &&
        1 <= size0 && size0 + 1 <= Maxsize && a == a0 &&
        pos == Vint (IntRepr (pos0)) && 
        store_int_array(a0, Hl, Maxsize)
      Ensure 
        exists Hl_final pos1,
          pos == Vint (IntRepr (pos1)) && 
          up(Hl, size0, pos0, pos1, Hl_final) && 
          store_int_array(a0, Hl_final, Maxsize)
  */

  /*@ Inv
        exists Hl0 pos1, 
          all_int(Hl) && 2 <= Maxsize && Maxsize <= INT_MAX &&
          1 <= pos0 && pos0 <= size0 &&
          1 <= size0 && size0 + 1 <= Maxsize &&   
          1 <= pos1 && pos1 <= size0 && a == a0 &&
          pos == Vint (IntRepr (pos1)) && 
          up(Hl, size0, pos0, pos1, Hl0) &&
          store_int_array(a0, Hl0, Maxsize)
  */
  while (pos > 1) {
    if (a[pos] <= a[pos >> 1]) {
      break;
    }
    swap(&a[pos], &a[pos >> 1]);
    pos >>= 1;
  }
}

void down(int *a, int size, int pos) {
  /*@ With Hl Maxsize size0 pos0 a0
      Require 
        all_int(Hl) && 2 <= Maxsize && Maxsize <= INT_MAX &&
        1 <= pos0 && pos0 <= size0 &&
        1 <= size0 && size0 + 1 <= Maxsize && a == a0 &&
        pos == Vint (IntRepr (pos0)) && 
        size == Vint (IntRepr (size0)) &&  
        store_int_array(a0, Hl, Maxsize)
      Ensure 
        exists Hl_final pos1,
          pos1 <= size0 && 
          down(Hl, size0, pos0, pos1, Hl_final) && 
          store_int_array(a0, Hl_final, Maxsize)
  */

  /*@ Inv
        exists Hl0 pos1, 
          all_int(Hl) && 2 <= Maxsize && Maxsize <= INT_MAX &&
          1 <= pos0 && pos0 <= size0 &&
          1 <= size0 && size0 + 1 <= Maxsize &&   
          1 <= pos1 && pos1 <= size0 && a == a0 &&
          pos1 <= size0 && 
          pos == Vint (IntRepr (pos1)) &&
          size == Vint (IntRepr (size0)) &&  
          down(Hl, size0, pos0, pos1, Hl0) &&
          store_int_array(a0, Hl0, Maxsize)
  */
  while (pos << 1 <= size) {
    int t;
    t = pos;
    if (a[pos << 1] > a[t]) {
      t = pos << 1;
    }
    if ((pos << 1 | 1) <= size) {
      if (a[pos << 1 | 1] > a[t]) {
        t = pos << 1 | 1;
      }
    }
    if (t == pos) {
      break;
    }
    swap(&a[pos], &a[t]);
    pos = t;
  }
}

void push(int *a, int *size, int val) {
  /*@ With Hl Maxsize size0 size_p val0 a0
      Require 
        all_int(Hl) && 1 <= Maxsize && Maxsize <= INT_MAX &&
        0 <= size0 && size0 + 1 + 1 <= Maxsize && a0 == a && 
        val == Vint (IntRepr (val0)) && 
        size == size_p && 
        store_int_array(a0, Hl, Maxsize) * store_int(size_p, size0)
      Ensure 
        exists Hl_final,
          val == Vint (IntRepr (val0)) && 
          size == size_p && 
          push(Hl, size0, val0, Hl_final) && 
          store_int_array(a0, Hl_final, Maxsize) * store_int(size_p, size0 + 1)
  */
  (*size) = (*size) + 1;
  a[*size] = val;
  up(a, *size);
}

int pop(int *a, int *size) {
  /*@ With Hl Maxsize size0 size_p a0
      Require  
        all_int(Hl) && 1 <= Maxsize && Maxsize <= INT_MAX &&
        0 <= size0 && size0 + 1 <= Maxsize && a == a0 &&
        size == size_p && 
        store_int_array(a0, Hl, Maxsize) * store_int(size_p, size0)
      Ensure 
        exists Hl_final size1,
          __return == Vint (IntRepr (pop_result(Hl, size0))) && 
          size1 == pop_length(Hl, size0) && 
          pop(Hl, size0, Hl_final) && 
          store_int_array(a0, Hl_final, Maxsize) * store_int(size_p, size1)
  */
  if (*size == 0)
  {
    return -1;
  }
  a[1] = a[*size];
  --(*size);
  down(a, *size, 1);
  return 0;
}

int top(int *a) {
  /*@ With Hl Maxsize a0
      Require a == a0 && 2 <= Maxsize && Maxsize <= INT_MAX && store_int_array(a0, Hl, Maxsize)
      
      Ensure __return == Vint (IntRepr (Znth(1, Hl))) && store_int_array(a0, Hl, Maxsize)
  */
  return a[1];
}