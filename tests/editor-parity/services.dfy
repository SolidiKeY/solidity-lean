class Services {
  function helper(a: int, b: int): int { a+b }
  function caller(): int { this.helper(1,2) }
}
