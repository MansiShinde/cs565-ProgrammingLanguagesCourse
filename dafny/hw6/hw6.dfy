/* Question 1. (10 points) */
/* This method finds the largest index in an array that does not 
   contain a non-zero element.

   Provide an implementation that satisfies the given specification.
*/

	
method HighestNonZeroIndex(arr: array<int>) returns (result: int)
requires arr.Length > 0
requires exists i :: 0 <= i < arr.Length && arr[i] != 0
ensures 0 <= result < arr.Length ==> arr[result] != 0
ensures forall i| 0 <= result < i < arr.Length :: arr[i] == 0
{
  result := -1;
  var i := arr.Length - 1; // Start from the last index

  while (i >= 0 && arr[i] == 0)
   invariant (0 <= i < arr.Length -1 )  ==> arr[i+1] == 0
   invariant result == -1 ==> forall x :: 0 <= i < x < arr.Length ==> arr[x] == 0
   invariant exists j :: 0 <= j <= i && arr[j] != 0
   invariant result != -1 ==> arr[result] != 0
   decreases i
    {
       if(arr[i] != 0)
       {
           result := i;
           return;    
       }
       i := i - 1;
   }  
}

/* Question 2. (10 points)
   Complete the body of the method such that it satisfies the 
   provided post-condition. 
*/

method M (x0 : int) returns (x : int)
  ensures (x0 < 3 ==> x == 1) && (x0 >= 3 ==> x < x0)
{
  if x0 < 3 {
    x := 1;
  } else {
    x := x0 - 1;
  }
}

/* Question 3.  (15 points)
   
  This method takes a sequence of integers and returns a new sequence 
  containing its unique elements.  The properties to be verified 
  are (1) every element in the returned sequence is an element of the 
  original, and (2) all elements in the result are unique. 

  Provide the necessary invariants and decreases clauses to allow 
  Dafny to verify the implementation against the given specifications. 
 */

method Unique(a: seq<int>) returns (b: seq<int>)
  ensures forall k :: 0 <= k < |a| ==> a[k] in b
  ensures forall i, j :: 0 <= i < j < |b| ==> b[i] != b[j]
{
  var index := 0;
  b := [];
  while index < |a|
		invariant 0 <= index <= |a| 
    invariant forall k :: 0 <= k < index ==> a[k] in b 
    invariant forall i, j :: 0 <= i < j < |b| ==> b[i] != b[j]
  {
    if (a[index] !in b) {
      b := b + [a[index]];
    }
    assert a[index] in b;
    index := index + 1;
  }
  return b;
}

/* Question 4.  (15 points)

   This method returns the maximum value in its input array.  

   Provide the necessary invariants and decreases clauses to allow 
   Dafny to verify the implementation against the given specifications. 
*/

method Max(a: array<int>) returns (max: nat)
  requires a.Length > 0
  requires forall j :: 0<=j < a.Length ==> a[j] >= 0
  ensures forall j :: 0<=j < a.Length ==> a[j] <= max
  ensures exists j :: 0 <= j < a.Length && a[j] == max
{
  max := a[0];
  var i := 0;
  var max_index := 0;

  while (i < a.Length)
    invariant 0 <= i <= a.Length
    invariant max_index < a.Length
    invariant forall k :: 0 <= k < i ==> a[k] <= max
    invariant a[max_index] == max
    decreases a.Length - i
	 {
 	if (a[i] > max) {
	  max := a[i]; 
    max_index := i;
    }
     i := i + 1;
  }
}

/* Question 5.  (15 points)

   This method computes the GCD of its arguments.

   Provide the necessary invariants and decreases clauses to allow Dafny 
   to verify the implementation against the given specifications.  You will 
   need to define a function called "gcd" to complete the post-condition.

*/


function gcd(a: nat, b: nat): nat
  requires a > 0 && b > 0
{
  if a == b
    then a
  else if a < b
    then gcd(a, b-a)
  else gcd(a-b, b)
}

method GcdIterative(m: nat, n: nat) returns (res: nat)
  requires m >= 1
  requires n >= 1
  ensures res == gcd(m, n) 
{ 
    var m1: nat := m;
    var n1: nat := n;

  while (m1!=n1)
      invariant m1 >= 1 && n1 >= 1  // ensures m1 and n1 stays positive
      invariant gcd(m, n) == gcd(m1, n1) // ensures GCD holds
      decreases m1+n1
  {  
    if (m1 > n1) { 
      m1 := m1 - n1; 
    } 
    else { 
      n1 := n1 - m1;  
    }
 }
  res := m1;
}


/* Question 6.  (15 points)

   This method computes the product of its arguments.

   Provide the necessary invariants and decreases clauses to allow Dafny 
   to verify the implementation against the given specifications.  

*/

method Product (m: nat , n: nat ) returns ( res: nat )
	ensures res == m * n
{
  var m1: nat := m;
  res := 0;
  while m1 != 0
      invariant m1 <= m 
      invariant res == (m - m1) * n 
      decreases m1 
  {
    var n1: nat := n;
    while n1 != 0
      invariant n1 <=n  
      invariant res == (m - m1) * n + (n - n1)
      decreases n1
     {
      res := res + 1;
      n1 := n1 - 1;
     }
    m1 := m1 - 1;
  }
  
}


/* Question 7.  (10 points)

   This method returns the quotient and remainder when
   dividing its two arguments.

   Provide the necessary invariants and decreases clauses to allow Dafny 
   to verify the implementation against the given specifications.  

*/

method divide(x : nat, y : nat) returns (q : nat, r : nat)
	requires y > 0
  ensures q * y + r == x && r >= 0 && r < y
 {
  q := 0;
  r := x;

  while r >= y

    invariant r >= 0 && r <= x && q * y + r == x
    decreases r
	{

    r := r - y;
    q := q + 1;
	}
}


/* Question 8. (10 points)

   This method returns the result of computing 2^n, where
   n is the method's argument.

   Provide the necessary invariants and decreases clauses to allow Dafny 
   to verify the implementation.  You will to provide the definition of
   function `pow` to complete the proof.
*/

function pow(A:int, N:nat):int
{
	if (N==0) then 1 else A * pow(A,N-1)
}

method power (n: nat) returns ( j: nat)
  ensures j == pow(2,n)
{
  var k := 0; j := 1;
	while k < n
    invariant 0 <= k <= n 
    invariant j == pow(2, k) 
    decreases n - k 
  {
   k := k + 1;
   j := 2 * j;
	}
}


