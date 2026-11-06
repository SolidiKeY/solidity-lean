class HoverCases {
  var x: int;
  /** Add values. */
  function helper(a: int): int { a }
  method run() {
    var x := true;
    { var x := 1; var inside := x; }
    var outside := x;
    var result := this.helper(this.x);
  }
}
