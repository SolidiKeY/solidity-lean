object "Root" {
  code {
    datacopy(0, dataoffset("payload"), datasize("payload"))
    return(0, datasize("payload"))
  }
  data "payload" hex"112233"
}
