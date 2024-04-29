/**
  * primebuffer 
  * @author Andrei Tudor Popescu | ID: 1668161
  * @author Alexia Bojian | ID: 1708112
  */

class PrimeBuffer {

  var db: set<nat>

  ghost predicate Valid()
    reads this
  {
    forall nr: nat | nr in db :: prime(nr)
  }

  constructor()
    ensures db == {}
    ensures Valid()
  {
    db := {};
  }

  constructor CreatePrimeBuffer(primes: seq<nat>)
    requires forall nr | nr in primes :: prime(nr)
    ensures forall nr | nr in db :: nr in primes
    ensures forall nr | nr in primes :: nr in db
    ensures Valid()
  {
    db := set temp | temp in primes :: temp;
  }

  method CheckPrime(n: nat) returns (p: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures p == prime(n)
    ensures p ==> n in db
    ensures db == old(db) || (p && n !in old(db) && db == old(db) + {n})
  {
    if(n in db) {
      return true;
    }

    p := IsPrime(n);
    if(p) {
      db := db + {n};
    }
  }

}

ghost predicate prime(n: nat) {
  n > 1 && (forall d: nat | 1 < d < n :: n % d != 0)
}

method IsPrime(n: nat) returns (p: bool)
  ensures p == prime(n)
{

  if(n <= 1)
  {
    return false;
  }
  if(n == 2)
  {
    return true;
  }

  p := true;
  var i: nat := 2;

  while(i < n)
    invariant 2 <= i <= n
    invariant p == forall d: nat | 1 < d < i :: n % d != 0
  {
    if(n % i == 0) {
      p := false;
    }

    i := i + 1;
  }
}

method TestPrimes() {
  var pb: PrimeBuffer := new PrimeBuffer();
  assert pb.db == {};

  var test: bool := pb.CheckPrime(2);
  assert test;
  assert pb.db == {2};

  assert 20 % 2 == 0;
  test := pb.CheckPrime(20);
  assert !test;
  assert pb.db == {2};

  test := pb.CheckPrime(13);
  assert test;
  assert pb.db != {2};
  assert pb.db == {2, 13};

  var pb2: PrimeBuffer := new PrimeBuffer.CreatePrimeBuffer([2, 3, 5, 7, 11, 13]);
  assert pb2.db != {};
  assert pb2.db == {2, 3, 5, 7, 11, 13};
  assert forall nr: nat | nr in pb2.db :: prime(nr);

  test := pb2.CheckPrime(13);
  assert test;
  assert pb2.db == {2, 3, 5, 7, 11, 13};

  var n :nat :| n > 1 && forall d: nat | 1 < d < n :: n % d != 0; // n is a prime number

  assert prime(n);
  test := pb2.CheckPrime(n);
  assert test;
  assert pb2.db == {2, 3, 5, 7, 11, 13, n};

  test := pb.CheckPrime(n);
  assert pb.db == {2, 13, n};
}