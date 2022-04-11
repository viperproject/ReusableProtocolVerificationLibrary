package library

import (
	bytes "bytes"
	"errors"
	fmt "fmt"
)


//@ trusted
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
//@ ensures res != nil
func NewError(desc string) (res error) {
	return errors.New("idB does not match")
}

//@ trusted
func Println(msg string) {
	fmt.Println(msg)
}

//@ trusted
//@ requires acc(Mem(na), 1/16)
//@ requires acc(Mem(receivedNb), 1/16)
//@ ensures  acc(Mem(na), 1/16)
//@ ensures  acc(Mem(receivedNb), 1/16)
func PrintInitiatorSuccess(na, receivedNb ByteString) {
	fmt.Println("A has successfully finished the protocol run")
	fmt.Println("A.na: ", na)
	fmt.Println("A.nb: ", receivedNb)
}

//@ trusted
//@ requires acc(Mem(receivedNa), 1/16)
//@ requires acc(Mem(nb), 1/16)
//@ ensures  acc(Mem(receivedNa), 1/16)
//@ ensures  acc(Mem(nb), 1/16)
func PrintResponderSuccess(receivedNa, nb ByteString) {
	fmt.Println("B has successfully finished the protocol run")
	fmt.Println("B.na: ", receivedNa)
	fmt.Println("B.nb: ", nb)
}
