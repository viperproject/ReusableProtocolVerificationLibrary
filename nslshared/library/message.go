package library

import (
	"encoding/binary"
	"errors"
	lib "gitlab.inf.ethz.ch/arquintl/prototrace/labeledlibrary/library"
	//@ tm "gitlab.inf.ethz.ch/arquintl/prototrace/term"
)

type Msg1 struct {
	Na lib.ByteString
	IdA string
}

type Msg2 struct {
	Na lib.ByteString
	Nb lib.ByteString
	IdB string
}

type Msg3 struct {
	Nb lib.ByteString
}

//@ requires acc(msg, 1/16)
//@ requires acc(lib.Mem(msg.Na), 1/16) && lib.Size(msg.Na) == lib.NonceLength
//@ ensures  acc(msg, 1/16)
//@ ensures  acc(lib.Mem(msg.Na), 1/16)
//@ ensures  lib.Mem(res) && lib.Size(res) >= 4 + lib.Size(msg.Na)
//@ ensures  lib.Abs(res) == tm.tuple3B(tm.integer32B(1), lib.Abs(msg.Na), tm.stringB(msg.IdA))
func MarshalMsg1(msg *Msg1) (res lib.ByteString) {
	idA := []byte(msg.IdA)
	var buff []byte = make([]byte, 4 + len(msg.Na) + len(idA))

	fieldTag := buff[:4]
	fieldNonce := buff[4:4+lib.NonceLength]
	fieldSender := buff[4+lib.NonceLength:]

	binary.LittleEndian.PutUint32(fieldTag, 1)
	copy(fieldNonce, msg.Na)
	copy(fieldSender, idA)
	
	return buff
}

//@ requires acc(lib.Mem(packet), 1/16)
//@ ensures  acc(lib.Mem(packet), 1/16)
//@ ensures  err == nil ==> lib.Size(packet) >= 4 + lib.NonceLength
//@ ensures  err == nil ==> acc(msg) && lib.Mem(msg.Na) && lib.Size(msg.Na) == lib.NonceLength
//@ ensures  err == nil ==> lib.Abs(packet) == tm.tuple3B(tm.integer32B(1), lib.Abs(msg.Na), tm.stringB(msg.IdA))
func UnmarshalMsg1(packet lib.ByteString) (msg *Msg1, err error) {
	if len(packet) < 4 + lib.NonceLength {
		return nil, errors.New("Packet is too short to be msg1")
	}

	tag := binary.LittleEndian.Uint32(packet[:4])
	if tag != 1 {
		return nil, errors.New("Unexpected tag to be msg1")
	}

	msg = &Msg1{
		Na: make([]byte, lib.NonceLength),
		IdA: string(packet[4+lib.NonceLength:]),
	}

	naLength := copy(msg.Na, packet[4:4+lib.NonceLength])

	if (naLength != lib.NonceLength) {
		return nil, errors.New("Copying nonce na failed")
	}
	return msg, nil
}

//@ requires acc(msg, 1/16)
//@ requires acc(lib.Mem(msg.Na), 1/16) && lib.Size(msg.Na) == lib.NonceLength
//@ requires acc(lib.Mem(msg.Nb), 1/16) && lib.Size(msg.Nb) == lib.NonceLength
//@ ensures  acc(msg, 1/16)
//@ ensures  acc(lib.Mem(msg.Na), 1/16)
//@ ensures  acc(lib.Mem(msg.Nb), 1/16)
//@ ensures  lib.Mem(res) && lib.Size(res) >= 4 + lib.Size(msg.Na) + lib.Size(msg.Nb)
//@ ensures  lib.Abs(res) == tm.tuple4B(tm.integer32B(2), lib.Abs(msg.Na), lib.Abs(msg.Nb), tm.stringB(msg.IdB))
func MarshalMsg2(msg *Msg2) (res lib.ByteString) {
	idB := []byte(msg.IdB)
	var buff []byte = make([]byte, 4 + len(msg.Na) + len(msg.Nb) + len(idB))

	fieldTag := buff[:4]
	fieldNa := buff[4:4+lib.NonceLength]
	fieldNb := buff[4+lib.NonceLength : 4+2*lib.NonceLength]
	fieldSender := buff[4+2*lib.NonceLength:]

	binary.LittleEndian.PutUint32(fieldTag, 2)
	copy(fieldNa, msg.Na)
	copy(fieldNb, msg.Nb)
	copy(fieldSender, idB)
	
	return buff
}

//@ requires acc(lib.Mem(packet), 1/16)
//@ ensures  acc(lib.Mem(packet), 1/16)
//@ ensures  err == nil ==> lib.Size(packet) >= 4 + 2 * lib.NonceLength
//@ ensures  err == nil ==> acc(msg)
//@ ensures  err == nil ==> lib.Mem(msg.Na) && lib.Size(msg.Na) == lib.NonceLength
//@ ensures  err == nil ==> lib.Mem(msg.Nb) && lib.Size(msg.Nb) == lib.NonceLength
//@ ensures  err == nil ==> lib.Abs(packet) == tm.tuple4B(tm.integer32B(2), lib.Abs(msg.Na), lib.Abs(msg.Nb), tm.stringB(msg.IdB))
func UnmarshalMsg2(packet lib.ByteString) (msg *Msg2, err error) {
	if len(packet) < 4 + 2 * lib.NonceLength {
		return nil, errors.New("Packet is too short to be msg2")
	}

	tag := binary.LittleEndian.Uint32(packet[:4])
	if tag != 2 {
		return nil, errors.New("Unexpected tag to be msg2")
	}

	msg = &Msg2{
		Na: make([]byte, lib.NonceLength),
		Nb: make([]byte, lib.NonceLength),
		IdB: string(packet[4+2*lib.NonceLength:]),
	}

	naLength := copy(msg.Na, packet[4:4+lib.NonceLength])
	nbLength := copy(msg.Nb, packet[4+lib.NonceLength:4+2*lib.NonceLength])

	if (naLength != lib.NonceLength || nbLength != lib.NonceLength) {
		return nil, errors.New("Copying nonce na or nb failed")
	}
	return msg, nil
}

//@ requires acc(msg, 1/16)
//@ requires acc(lib.Mem(msg.Nb), 1/16) && lib.Size(msg.Nb) == lib.NonceLength
//@ ensures  acc(msg, 1/16)
//@ ensures  acc(lib.Mem(msg.Nb), 1/16)
//@ ensures  lib.Mem(res) && lib.Size(res) == 4 + lib.Size(msg.Nb)
//@ ensures  lib.Abs(res) == tm.tuple2B(tm.integer32B(3), lib.Abs(msg.Nb))
func MarshalMsg3(msg *Msg3) (res lib.ByteString) {
	var buff []byte = make([]byte, 4 + len(msg.Nb))

	fieldTag := buff[:4]
	fieldNb := buff[4:]

	binary.LittleEndian.PutUint32(fieldTag, 3)
	copy(fieldNb, msg.Nb)
	
	return buff
}

//@ requires acc(lib.Mem(packet), 1/16)
//@ ensures  acc(lib.Mem(packet), 1/16)
//@ ensures  err == nil ==> lib.Size(packet) >= 4 + lib.NonceLength
//@ ensures  err == nil ==> acc(msg)
//@ ensures  err == nil ==> lib.Mem(msg.Nb) && lib.Size(msg.Nb) == lib.NonceLength
//@ ensures  err == nil ==> lib.Abs(packet) == tm.tuple2B(tm.integer32B(3), lib.Abs(msg.Nb))
func UnmarshalMsg3(packet lib.ByteString) (msg *Msg3, err error) {
	if len(packet) < 4 + lib.NonceLength {
		return nil, errors.New("Packet is too short to be msg3")
	}

	tag := binary.LittleEndian.Uint32(packet[:4])
	if tag != 3 {
		return nil, errors.New("Unexpected tag to be msg2")
	}

	msg = &Msg3{
		Nb: make([]byte, lib.NonceLength),
	}

	nbLength := copy(msg.Nb, packet[4:4+lib.NonceLength])

	if (nbLength != lib.NonceLength) {
		return nil, errors.New("Copying nonce nb failed")
	}
	return msg, nil
}
