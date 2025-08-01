package library

import (
	bytes "bytes"
	"errors"
	fmt "fmt"
)

//@ trusted
//@ decreases
//@ requires acc(Mem(s1), 1/16)
//@ requires acc(Mem(s2), 1/16)
//@ ensures  acc(Mem(s1), 1/16)
//@ ensures  acc(Mem(s2), 1/16)
// ensures  res ==> Size(s1) == Size(s2)
//@ ensures  res == (Abs(s1) == Abs(s2))
// ensures  res ==> unfolding acc(Mem(s1), 1/16) in unfolding acc(Mem(s2), 1/16) in forall i int :: { s1[i], s2[i] } 0 <= i && i < len(s1) ==> s1[i] == s2[i]
func Compare(s1, s2 ByteString) (res bool) {
	return bytes.Compare(s1, s2) == 0
}

//@ trusted
//@ decreases
//@ ensures res != nil
func NewError(desc string) (res error) {
	return errors.New(desc)
}

/*@
ghost
trusted
decreases
ensures res != nil
func AttackerNewError(desc string) (res error) {
	return errors.New(desc)
}
@*/

//@ trusted
//@ decreases
func Println(msg string) {
	fmt.Println(msg)
}
