/*
TwoWaySort: Sorting of boolean array where two pointers i and j move
            from the beginning and end of array, respectively, and
            swapping of values pointed to by i and j takes place as needed.
1. Safety: Verify that every array access is made within bounds.
2. Termination: Prove that function TwoWaySort always terminates.
3. Behavior: Verify that after execution of function TwoWaySort, 
             the following properties hold:
             (a) array is a permutation of its initial contents.
             (b) array is sorted in increasing order. (I'm working on this 
                 last one, trying to figure out how to write an ensures 
                 statement that can check whether a boolean array is sorted 
                 since <= doesn't work on bool values so have to think of 
                 some other way to compare).
*/

function total(a: array<bool>, i:int, key: bool): int
requires a != null;
reads a;
{
	if i < 0
  		then 0
 	else if (a.Length == 0)
  		then 0
  	else if 0<=i<a.Length && a[i] == key
  		then total(a, i-1, key) + 1
  	else total(a, i-1, key)
}

predicate compare(a: array<bool>, a1: array<bool>)
reads a;
reads a1;
requires a != null;
requires a1 != null;
{
	forall key:bool :: total(a, a.Length, key) == total(a1, a1.Length, key)
}

method TwoWaySort(a:array<bool>)
  requires a != null;
  modifies a;
  ensures compare(a, old(a));
  //ensures forall k:: forall l:: 0 <= k < l < a.Length ==> a[k] <= a[l]; working on this
{
	var i:int := 0;
	var j:int := a.Length - 1;
	while (i <= j)
	invariant 0 <= i <= (j+1);
	invariant (i-1) <= j < a.Length;	
	decreases (j+1) - i;
	decreases j - (i-1);
	{
		if a[i] == false 
		{
			i := i + 1;
		}
		else if a[j] == true 
		{
			j := j - 1;
		}
		else
		{
		    var t:bool := a[i];
	        a[i] := a[j];
    	    a[j] := t;
			i := i + 1;
			j := j - 1;
		}
	}
}

method Main() 
{
  var a := new bool[3];
  a[0] := false;
  a[1] := true;
  a[2] := false;
  TwoWaySort(a);
  
  var i:int := 0;
  while (i < a.Length)
  {
    print a[i];
    i := i + 1;
  }
  //prints sorted array as false,false,true 
}
