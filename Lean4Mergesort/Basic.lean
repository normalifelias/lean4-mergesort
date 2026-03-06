def myMerge {α} (le : α → α → Bool) (xs ys : Array α) (ix iy : Nat) (work : Array α) (hwork : work.size = xs.size + ys.size) (hix : ix ≤ xs.size) (hiy : iy ≤ ys.size): { merged : Array α // merged.size = work.size } :=
  if hix : ix < xs.size then
    if hiy : iy < ys.size then
      if le xs[ix] ys[iy]
        then ⟨myMerge le xs ys (ix + 1) iy (work.set (ix+iy) xs[ix]) (by grind) (by grind) (by grind), (by grind)⟩
        else ⟨myMerge le xs ys ix (iy + 1) (work.set (ix+iy) ys[iy]) (by grind) (by grind) (by grind), (by grind)⟩
    else
      ⟨myMerge le xs ys (ix + 1) iy (work.set (ix+iy) xs[ix]) (by grind) (by grind) (by grind), (by grind)⟩
  else
    if hiy : iy < ys.size then
      ⟨myMerge le xs ys ix (iy + 1) (work.set (ix+iy) ys[iy]) (by grind) (by grind) (by grind), (by grind)⟩
    else
      ⟨work, rfl⟩

def myMergeSort1 (xs aux : Array α) (le : α → α → Bool) (haux : xs.size = aux.size): { sorted : Array α // sorted.size = xs.size } :=
  if h : xs.size ≤ 1
  then ⟨xs, rfl⟩
  else
    let mid := xs.size / 2
    let left := myMergeSort1 (xs.take mid) (aux.take mid) le (by grind)
    let right := myMergeSort1 (xs.drop mid) (aux.drop mid) le (by grind)
    have hlr : aux.size = left.val.size + right.val.size := by grind
    ⟨myMerge le left.val right.val 0 0 aux hlr (by grind) (by grind), (by grind)⟩


def le_Nat (x y : Nat): Bool := x ≤ y
def testValues : Array Nat := #[47, 13, 82, 6, 91, 34, 57, 23, 76, 41]
#eval myMergeSort1 testValues testValues le_Nat rfl

--this is not tail-recursive, so left and right are newly allocated every time!
--> New idea: Bottom-up mergesort

def copyFinalSlice (inp out : Array α) (start : Nat) : Array α :=
  if h : start < inp.size then --arrived at end?
    copyFinalSlice inp (out.set! start inp[start]) (start + 1) --copy current value to same position in out, increase current index
  else
    out --if there is nothing left to copy, return

def myMerge_sliced {α} [Inhabited α] (le : α → α → Bool) (inp : Array α) (start mid last ix iy : Nat) (work : Array α) : Array α := --variation of myMerge w/o indexing proofs and on two full arrays, replacing xs and ys by slicing indices
  if ix < (mid - start) then --xs finished? (ix < len xs)
    if iy < (last - mid) then --ys finished? (iy < len ys)
      if le inp[start+ix]! inp[mid+iy]! --comparison
        then myMerge_sliced le inp start mid last (ix + 1) iy (work.set! (ix+iy+start) inp[start+ix]!) --if xs[ix] is smaller, it is written to the output at the correct location
        else myMerge_sliced le inp start mid last ix (iy + 1) (work.set! (ix+iy+start) inp[mid+iy]!) -- else, it's ys[iy]
    else
      myMerge_sliced le inp start mid last (ix + 1) iy (work.set! (ix+iy+start) inp[start+ix]!) --if ys is done, but not xs, the next element from xs is copied
  else
    if iy < (last - mid) then --ys finished?
      myMerge_sliced le inp start mid last ix (iy + 1) (work.set! (ix+iy+start) inp[mid+iy]!) --if xs is done, but not ys, the next element from ys is copied
    else
      work --if both slices are done, return

partial def mMS2_helper [Inhabited α] (le : α → α → Bool) (arr1 arr2 : Array α) (i width : Nat) : Array α :=
    if width < arr1.size then --outer loop: runs till the whole list has been merged over
      if i < arr1.size then --inner loop: goes through all the couples to merge, then increases i (the start marker) by the range that was just processed
        if i + width < arr1.size then --only merge if there is a counterpart to merge with
          if i + 2 * width > arr1.size then --if the counterpart is shorter, no problem, just use it
            mMS2_helper le arr1 (myMerge_sliced le arr1 i (i+width) arr1.size 0 0 arr2) (i+2*width) width --special case: counterpart is shorter
          else mMS2_helper le arr1 (myMerge_sliced le arr1 i (i+width) (i+2*width) 0 0 arr2) (i+2*width) width --normal case
        else mMS2_helper le arr1 (copyFinalSlice arr1 arr2 i) (i+2*width) width --special case: no counterpart => the already sorted portion is carried over
      else mMS2_helper le arr2 arr1 0 (2*width) --if all couples have been merged, switch arrays and merge those with their new counterparts
    else arr1

def myMergeSort2 [Inhabited α] (xs : Array α) (le : α → α → Bool) : Array α :=
  mMS2_helper le xs xs 0 1 --copy xs one time as an auxiliary array, initialise i and width


def testValues2 : Array Nat := #[47, 13, 82, 6, 91, 34, 57, 23, 76, 41, 88, 3, 65, 29, 54, 17, 72, 39, 84, 11, 63, 28, 95, 42, 7, 56, 31, 78, 19, 67, 44, 90, 25, 58, 14, 83, 37, 62, 9, 71, 48, 26, 93, 15, 52, 38, 77, 22, 69, 4, 86, 33, 61, 18, 45, 79, 12, 57, 35, 81, 24, 68, 43, 96, 8, 53, 27, 74, 16, 89, 41, 64, 30, 55, 20, 73, 46, 85, 10, 60, 36, 92, 21, 49, 66, 32, 75, 5, 87, 40, 59, 28, 70, 38, 94, 50, 80, 2, 97, 44]
#eval myMergeSort2 testValues2 le_Nat
#eval (myMergeSort1 testValues2 testValues2 le_Nat (by decide) = myMergeSort2 testValues2 le_Nat)
