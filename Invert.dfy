/*
Invert:     Invert an injective array A on N elements in the 
		    subrange from 0 to N − 1, i.e., the output array B 
		    must be such that B[A[i]] = i for 0 <= i < N.
		    You can assume that A is surjective.
Properties: Show that the resulting array is also injective. For
			bonus points, you can demonstrate other properties, 
			e.g., that A and B are inverses.
*/

method Invert(a: array<int>, b: array<int>)
  requires a != b;
  requires a != null;
  requires b != null;
  requires a.Length == b.Length;
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i] < a.Length;
  requires forall i, j:: 0 <= i < a.Length && 0 <= j < a.Length && i != j ==> a[i] != a[j];
  ensures forall i :: 0 <= i < a.Length
                      && 0 <= a[i] < b.Length 
                      ==> b[a[i]] == i; 
  modifies b;
{	
	var i:int := 0; 
	while (i < a.Length) 
	invariant a.Length == b.Length;
	invariant 0 <= i <= b.Length;
	invariant 0 <= i <= a.Length;
	decreases a.Length-i;
	modifies b;
    invariant forall j:: 0 <= j < a.Length ==> 0 <= a[j] < b.Length;
	invariant forall k:: 0 <= k < i <= a.Length ==> b[a[k]] == k; 
	{
		b[a[i]] := i;
		assert (b[a[i]] == i);
		i := i + 1;
	}
}

method Main() 
{  
  // Test case: If array A is: [9, 3, 8, 2, 7, 4, 0, 1, 5, 6]
  // then output B should be: [6, 7, 3, 1, 5, 8, 9, 4, 2, 0]

  var a := new int[10];
  a[0] := 9;
  a[1] := 3;
  a[2] := 8;
  a[3] := 2;
  a[4] := 7;
  a[5] := 4;
  a[6] := 0;
  a[7] := 1;
  a[8] := 5;
  a[9] := 6;
  
  var b := new int[10];
  Invert(a, b);
     
  var i:int := 0;
  while(i < b.Length)
  {
    print b[i];
    print " ";
    i := i + 1;
  }
  
  // prints expected output array: [6, 7, 3, 1, 5, 8, 9, 4, 2, 0]
}
