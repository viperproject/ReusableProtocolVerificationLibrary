package library

import (
	"encoding/binary"
	"errors"
	lib "gitlab.inf.ethz.ch/arquintl/prototrace/labeledlibrary/library"
	tm "gitlab.inf.ethz.ch/arquintl/prototrace/term"
)

type Msg1 struct {
	na lib.ByteString
	idA string
}

type Msg2 struct {
	na lib.ByteString
	nb lib.ByteString
	idB string
}

type Msg3 struct {
	nb lib.ByteString
}

//@ requires acc(msg, 1/16)
//@ requires acc(lib.Mem(msg.na), 1/16) && lib.Size(msg.na) == lib.NonceLength
//@ ensures  acc(msg, 1/16)
//@ ensures  acc(lib.Mem(msg.na), 1/16)
//@ ensures  lib.Mem(res) && lib.Size(res) >= 4 + lib.Size(msg.na)
//@ ensures  lib.Abs(res) == tm.tuple3B(tm.integer32B(1), lib.Abs(msg.na), tm.stringB(msg.idA))
func MarshalMsg1(msg *Msg1) (res lib.ByteString) {
	idA := []byte(msg.idA)
	var buff []byte = make([]byte, 4 + len(msg.na) + len(idA))

	fieldTag := buff[:4]
	fieldNonce := buff[4:4+lib.NonceLength]
	fieldSender := buff[4+lib.NonceLength:]

	binary.LittleEndian.PutUint32(fieldTag, 1)
	copy(fieldNonce, msg.na)
	copy(fieldSender, idA)
	
	return buff
}

//@ requires acc(lib.Mem(packet), 1/16)
//@ ensures  acc(lib.Mem(packet), 1/16)
//@ ensures  err == nil ==> lib.Size(packet) >= 4 + lib.NonceLength
//@ ensures  err == nil ==> acc(msg) && lib.Mem(msg.na) && lib.Size(msg.na) == lib.NonceLength
//@ ensures  err == nil ==> lib.Abs(packet) == tm.tuple3B(tm.integer32B(1), lib.Abs(msg.na), tm.stringB(msg.idA))
func UnmarshalMsg1(packet lib.ByteString) (msg *Msg1, err error) {
	if len(packet) < 4 + lib.NonceLength {
		return nil, errors.New("Packet is too short to be msg1")
	}

	tag := binary.LittleEndian.Uint32(packet[:4])
	if tag != 1 {
		return nil, errors.New("Unexpected tag to be msg1")
	}

	msg = &Msg1{
		na: make([]byte, lib.NonceLength),
		idA: string(packet[4+lib.NonceLength:]),
	}

	naLength := copy(msg.na, packet[4:4+lib.NonceLength])

	if (naLength != lib.NonceLength) {
		return nil, errors.New("Copying nonce na failed")
	}
	return msg, nil
}

//@ requires acc(msg, 1/16)
//@ requires acc(lib.Mem(msg.na), 1/16) && lib.Size(msg.na) == lib.NonceLength
//@ requires acc(lib.Mem(msg.nb), 1/16) && lib.Size(msg.nb) == lib.NonceLength
//@ ensures  acc(msg, 1/16)
//@ ensures  acc(lib.Mem(msg.na), 1/16)
//@ ensures  acc(lib.Mem(msg.nb), 1/16)
//@ ensures  lib.Mem(res) && lib.Size(res) >= 4 + lib.Size(msg.na) + lib.Size(msg.nb)
//@ ensures  lib.Abs(res) == tm.tuple4B(tm.integer32B(2), lib.Abs(msg.na), lib.Abs(msg.nb), tm.stringB(msg.idB))
func MarshalMsg2(msg *Msg2) (res lib.ByteString) {
	idB := []byte(msg.idB)
	var buff []byte = make([]byte, 4 + len(msg.na) + len(msg.nb) + len(idB))

	fieldTag := buff[:4]
	fieldNa := buff[4:4+lib.NonceLength]
	fieldNb := buff[4+lib.NonceLength : 4+2*lib.NonceLength]
	fieldSender := buff[4+2*lib.NonceLength:]

	binary.LittleEndian.PutUint32(fieldTag, 2)
	copy(fieldNa, msg.na)
	copy(fieldNb, msg.nb)
	copy(fieldSender, idB)
	
	return buff
}

//@ requires acc(lib.Mem(packet), 1/16)
//@ ensures  acc(lib.Mem(packet), 1/16)
//@ ensures  err == nil ==> lib.Size(packet) >= 4 + 2 * lib.NonceLength
//@ ensures  err == nil ==> acc(msg)
//@ ensures  err == nil ==> lib.Mem(msg.na) && lib.Size(msg.na) == lib.NonceLength
//@ ensures  err == nil ==> lib.Mem(msg.nb) && lib.Size(msg.nb) == lib.NonceLength
//@ ensures  err == nil ==> lib.Abs(packet) == tm.tuple4B(tm.integer32B(2), lib.Abs(msg.na), lib.Abs(msg.nb), tm.stringB(msg.idB))
func UnmarshalMsg2(packet lib.ByteString) (msg *Msg2, err error) {
	if len(packet) < 4 + 2 * lib.NonceLength {
		return nil, errors.New("Packet is too short to be msg2")
	}

	tag := binary.LittleEndian.Uint32(packet[:4])
	if tag != 2 {
		return nil, errors.New("Unexpected tag to be msg2")
	}

	msg = &Msg2{
		na: make([]byte, lib.NonceLength),
		nb: make([]byte, lib.NonceLength),
		idA: string(packet[4+2*lib.NonceLength:]),
	}

	naLength := copy(msg.na, packet[4:4+lib.NonceLength])
	nbLength := copy(msg.nb, packet[4+lib.NonceLength:4+2*lib.NonceLength])

	if (naLength != lib.NonceLength || nbLength != lib.NonceLength) {
		return nil, errors.New("Copying nonce na or nb failed")
	}
	return msg, nil
}

//@ requires acc(msg, 1/16)
//@ requires acc(lib.Mem(msg.nb), 1/16) && lib.Size(msg.nb) == lib.NonceLength
//@ ensures  acc(msg, 1/16)
//@ ensures  acc(lib.Mem(msg.nb), 1/16)
//@ ensures  lib.Mem(res) && lib.Size(res) == 4 + lib.Size(msg.nb)
//@ ensures  lib.Abs(res) == tm.tuple2B(tm.integer32B(3), lib.Abs(msg.nb))
func MarshalMsg3(msg *Msg3) (res lib.ByteString) {
	var buff []byte = make([]byte, 4 + len(msg.nb))

	fieldTag := buff[:4]
	fieldNb := buff[4:]

	binary.LittleEndian.PutUint32(fieldTag, 3)
	copy(fieldNb, msg.nb)
	
	return buff
}

//@ requires acc(lib.Mem(packet), 1/16)
//@ ensures  acc(lib.Mem(packet), 1/16)
//@ ensures  err == nil ==> lib.Size(packet) >= 4 + lib.NonceLength
//@ ensures  err == nil ==> acc(msg)
//@ ensures  err == nil ==> lib.Mem(msg.nb) && lib.Size(msg.nb) == lib.NonceLength
//@ ensures  err == nil ==> lib.Abs(packet) == tm.tuple2B(tm.integer32B(3), lib.Abs(msg.nb))
func UnmarshalMsg3(packet lib.ByteString) (msg *Msg3, err error) {
	if len(packet) < 4 + lib.NonceLength {
		return nil, errors.New("Packet is too short to be msg3")
	}

	tag := binary.LittleEndian.Uint32(packet[:4])
	if tag != 3 {
		return nil, errors.New("Unexpected tag to be msg2")
	}

	msg = &Msg3{
		nb: make([]byte, lib.NonceLength),
	}

	nbLength := copy(msg.nb, packet[4:4+lib.NonceLength])

	if (nbLength != lib.NonceLength) {
		return nil, errors.New("Copying nonce nb failed")
	}
	return msg, nil
}
