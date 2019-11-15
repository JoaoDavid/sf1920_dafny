class {:autocontracts} BoundedQueue<T(0)> {

    ghost var contents: seq<T>
    var q: array<T>
    var n: nat
    var first: nat
    var last: nat

    predicate Valid()
        reads this,q
    {
        0 <= n <= q.Length &&
        0 <= first < q.Length &&
        0 <= last < q.Length &&
        q.Length > 0 &&
        ((first == last) <==> (n == 0 || n == q.Length)) &&
        ((n > 0 && first < last) ==> (n == last - first)) &&
        ((n > 0 && first >= last) ==> (n == (q.Length + last - first))) &&
        (first < last ==> contents == q[first..last]) &&
        (first > last ==> contents == q[0..last] + q[first..q.Length]) && 
        (first == last && n == q.Length ==> contents == q[0..n]) &&
        (first == last && n == 0 ==> contents == [])
    }

    constructor (length : nat)
        requires length > 0
        ensures Valid()
        //ensures contents == []
    {
        q := new T[length];
        n := 0;
        first := 0;
        last := 0;
        contents := [];
    }

    function method IsEmpty(): bool
        //reads this,q
        requires Valid()
        ensures Valid()
        //ensures IsEmpty() <==> contents == []
        //ensures IsEmpty() ==> first == last
    {
        n == 0
    }

    
    function method IsFull(): bool
        //reads this,q
        requires Valid()
        ensures Valid()
        ensures IsFull() <==> n == q.Length
        //ensures !IsFull() ==> last > 0
    {
        n == q.Length
    }

    // Adds the item to this queue 
    method Enqueue(item: T)
        modifies this,q
        requires Valid()
        ensures Valid()
        requires !IsFull()
       // ensures q == old(q)
        /*ensures n < q.Length ==> !IsFull()
        ensures n == q.Length ==> IsFull()*/
    {  
        q[last] := item;
        //assert n != q.Length;
        if (first > last){            
            last := last + 1;
            n := n + 1;
            contents := q[0..last] + q[first..q.Length];
            //assert Valid();
        } else if (first < last) {
            if (last + 1 == q.Length){
                last := 0;
                n := n + 1;
                contents := q[first..q.Length];
            } else {
                last := last + 1;
                n := n + 1;
                contents := q[first..last];
            }
        } else { //first == last
            if (last + 1 == q.Length ){
                last := 0;
                n := n + 1;
                contents := q[first..q.Length];
                //assert n != 0; 
            } else {//when first == last == all index except q.Length - 1
                last := last + 1;
                n := n + 1;
                contents := q[first..last];
            }
        }
    }

    // Removes and returns the item on this queue that was least recently added 
    method Dequeue() returns (item: T)
        requires Valid()
        ensures Valid()
        requires !IsEmpty()
    {
        assert n > 0;
        item := q[first];
        if (first < last){            
            first := first + 1;
            n := n - 1;
            contents := q[first..last];
            //assert Valid();
        } else if (first > last) {
            if (first + 1 == q.Length){
                first := 0;
                n := n - 1;
                contents := q[first..last];
            } else {
                first := first + 1;
                n := n - 1;
                contents := q[0..last] + q[first..q.Length];
            }
        } else{ //first == last
            if (first + 1 == q.Length ){
                first := 0;
                n := n - 1;
                contents := q[first..last];
            } else {
                first := first + 1;
                n := n - 1;
                contents := q[0..last] + q[first..q.Length];
            }
        }
    }

    // Returns the item least recently added to this queue 
    function method Peek(): T
        //reads this,q
        requires Valid()
        ensures Valid()
        requires !IsEmpty()
        //ensures contents == old(contents)
    {   
        assert  0 <= first ;
        q[first]
    }

    //debug methods
    function method Size(): nat
        //reads this,q
        requires Valid()
        ensures Valid()
        //ensures contents == old(contents)
    {   
        n
    }

    method PrintQueue()
        //reads this,q
        requires Valid()
        ensures Valid()
        //ensures contents == old(contents)
    {   
        var i := 0;
        while(i < q.Length) {
            print q[i];
            print " : ";
            i := i + 1;
        }
        print "\n";
        print "first: "; print first;
        print "  last: "; print last;
        print "  n: "; print n;
    }

}

method Main() {
  print "BoundedQueue\n";
  var length := 3;
  var q := new BoundedQueue<int>(length);
  //---------------------
  if (!q.IsFull()){
    q.Enqueue(-1);
  }
  if (!q.IsFull()){
    q.Enqueue(-2);
  }
  if (!q.IsFull()){
    q.Enqueue(-3);
  }
  //full
  print "\nPrintQueue "; q.PrintQueue();
  if (!q.IsEmpty()){
    var e := q.Dequeue();
    print "\nElemDeq ";print(e);
  }
  if (!q.IsFull()){
    q.Enqueue(-11);
  }
  print "\nPrintQueue "; q.PrintQueue();
  if (!q.IsEmpty()){
    var e := q.Dequeue();
    print "\nElemDeq ";print(e);
  }
  
  if (!q.IsFull()){
    q.Enqueue(-12);
  }
  if (!q.IsFull()){
    q.Enqueue(-13);
  }
  print "\nPrintQueue "; q.PrintQueue();
  if (!q.IsEmpty()){
    var e := q.Dequeue();
    print "\nElemDeq ";print(e);
  }
  if (!q.IsEmpty()){
    var e := q.Dequeue();
    print "\nElemDeq ";print(e);
  }
  if (!q.IsEmpty()){
    var e := q.Dequeue();
    print "\nElemDeq ";print(e);
  }
    print "\nPrintQueue "; q.PrintQueue();
    if (!q.IsFull()){
    q.Enqueue(-21);
  }
if (!q.IsEmpty()){
    var e := q.Dequeue();
    print "\nElemDeq ";print(e);
  }



  print "\nPrintQueue "; q.PrintQueue();
}
