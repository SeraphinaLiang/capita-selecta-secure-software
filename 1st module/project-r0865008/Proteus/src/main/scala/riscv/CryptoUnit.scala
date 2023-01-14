package riscv

import spinal.core._

class CryptoUnit(implicit config: Config) extends Component {
  object Operation extends SpinalEnum {
    val ENCRYPT, DECRYPT = newElement()
  }

  val key = in UInt(config.xlen bits)
  val value = in UInt(config.xlen bits)
  val operation = in(Operation)
  val result = out UInt(config.xlen bits)

  switch (operation) {
    is (Operation.ENCRYPT) {
      result := (value + 1) ^ key
    }
    is (Operation.DECRYPT) {
      result := (value ^ key) - 1
    }
  }
}
