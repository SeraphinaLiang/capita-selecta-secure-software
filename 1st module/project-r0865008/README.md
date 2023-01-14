[[_TOC_]]

# Introduction

This project introduces a custom RISC-V processor under development at the
DistriNet research group. The goal of this processor is to create a highly
extensible and configurable RISC-V implementation that allows for easy
experimentation with hardware security extensions. It supports the RV32I base
ISA as well as the M-extension. Its implementation consists of about 4,000 lines
of SpinalHDL code which generates about 11,000 lines of Verilog.

The assignment for this project is to create a protection against return address
smashing by implementing a simple form of return address encryption. Before
going into the details, however, we will explain how to start using the custom
RISC-V processor and some necessary implementation details.

# Setup

## Prerequisites

Since the RISC-V processor is implemented using SpinalHDL, the same setup is
needed as for the SpinalHDL exercise session.

To compile C code to run on the processor, the [GNU toolchain for
RISC-V](https://github.com/riscv-collab/riscv-gnu-toolchain) is needed. It can
be compiled manually on Linux using the following commands:
```
$ git clone https://github.com/riscv-collab/riscv-gnu-toolchain.git
$ cd riscv-gnu-toolchain
$ git checkout 2022.10.11
$ ./configure --prefix=<path/to/install/directory> --with-arch=rv32im --with-abi=ilp32
$ make
```

Make sure to execute these command _exactly_ as above, replacing
`<path/to/install/directory>` with the location where you want the toolchain to
be installed. To use the toolchain, make sure to add
`<path/to/install/directory>/bin` to your `PATH`.

## Using the RISC-V processor

The `Examples` directory contains an example in assembly (`asm.s`) and an
example in C (`hello.c`). It also contains a Makefile that builds both examples
and generates flat binary (`*.bin`) and [Intel
HEX](https://en.wikipedia.org/wiki/Intel_HEX) (`*.ihex`) files.

The `Proteus` directory contains the processor implementation and all paths
mentioned in the remainder of this section are relative to it. There are two
ways to simulate the processor. First, simulations can be run directly from
Scala similar to how simulations were run during the exercise session. This is
implemented by the `riscv.CoreSim` main class which expects an Intel HEX version
of the binary to run as input:
```
$ sbt 'runMain riscv.CoreSim ../Examples/hello.ihex'
```

This main class can of course also be directly run from an IDE like IntelliJ.
The VCD file will be generated at `simWorkspace/Core/test.vcd`.

This way of simulating will rebuild the Verilog implementation every run. This
is exactly what is wanted while developing the processor itself but can be quite
slow if we just want to run different programs without changing the hardware in
between. To make the latter case more efficient, a standalone simulator binary
can be built as follows:
```
$ make -C sim
```

This will build a binary at `sim/build/sim` which can be run by providing it
with a flat binary file as input:
```
$ ./sim/build/sim ../Examples/hello.bin
```
When running the simulation this way, a VCD file called `sim.vcd` is generated.

# Pipeline implementation

The RISC-V processor used for this project is implemented as a classic 5-stage
[RISC](https://en.wikipedia.org/wiki/Classic_RISC_pipeline) pipeline. This
section, which explains the implementation, assumes basic knowledge of how such
a pipeline works.

The pipeline is built as a linear sequences of [stages](#stages) and in
principle, data is propagated each cycle from one stage to the next. At the end
of each stage, a set of pipeline registers stores the data from the preceding
stage to be used by the next stage. The propagation of the values in the
pipeline registers is managed by the [scheduling logic](#pipeline) which, among
other things, makes sure that hazards are resolved. The logic in the stages is
not fixed but instead is added dynamically when building the pipeline through
the use of [plugins](#plugins). Plugins typically create logic that reads the
data in the preceding pipeline registers, transforms them, and then stores the
results in the next pipeline registers. To ensure maximum reusability, plugins
can make their logic available to other plugins by exposing
[services](#services).

## Stages

Each pipeline stage is represented by an instantiation of the `Stage` class.
Although this class is a `Component` subclass, it does not contain any logic by
itself. All logic is added to the stages by plugins. The only functionality
implemented by the `Stage` class is reading input pipeline registers (written by
the previous stage) and writing output registers (to be read by the next stage).

To use this functionality, plugins can use the `input`, `output`, and `value`
methods of the `Stage` class. All these methods return a
[`Data`](https://spinalhdl.github.io/SpinalDoc-RTD/master/SpinalHDL/Data%20types)
subtype that can be used to read from or write to an input or output. Multiple
input and output registers can be added to stages and to identify which one
should be accessed, objects that subclass `PipelineData` are used.

The `value` method is similar to `input`. The difference is that when the
`output` has already been updated for a certain pipeline register, `value`
returns the updated value while `input` always returns the original input value.
In practice, `value` should almost always be used instead of `input`.

### PipelineData

`PipelineData` is a generic class that  wraps around a SpinalHDL `Data` subtype.
To use this class as an identity for pipeline registers, `object` identity is
used. For example, the predefined pipeline register to store the program counter
is defined as follows:
```scala
object PC extends PipelineData(UInt(32 bits))
```

The `object` called `PC` is used as the identifier passed to the `input`,
`output`, and `value` methods and, in this case, the return value of these
methods will have type `UInt`. See `PipelineData.scala` for all predefined
pipeline registers. The most important ones are the following:

- `IR` (`UInt(32 bits)`): instruction register;
- `RS1`/`RS2` (`UInt(5 bits)`): identifiers of `rs1` and `rs2`;
- `RS1_DATA`/`RS2_DATA` (`UInt(32 bits)`): values of `rs1` and `rs2`. Note that
  due to various data hazards, these values or not always valid (see later);
- `RD` (`UInt(5 bits)`): identifier of `rd`;
- `RD_DATA` (`UInt(32 bits)`): value to be written to `rd`;
- `WRITE_RD` (`Bool`): `True` if this instruction writes to `rd`;
- `RD_VALID` (`Bool`): `True` if `RD_DATA` is valid.

Of course, plugins are not restricted to the predefined pipeline registers and
can define new ones as needed.

For a pipeline register called `FOO`, the following Verilog signals are created
for each `Stage` that uses it: `in_FOO` (`input`), `out_FOO` (`output`), and
`value_FOO` (`value`). When inspecting the results of a simulation in GTKWave,
most information can be gathered from these signals.

### Pipeline register propagation

When building the [pipeline](#pipeline), logic is added that propagates pipeline
registers as needed. When an `input` is requested at a particular stage, it will
be propagated from the earliest stage where an `output` with the same identifier
is produced through all intermediate stages. If an `input` is requested at a
stage before the earliest `output` stage, an error is produced. This logic also
ensures that pipeline registers are not propagated further than the latest stage
where an `input` is requested in order to minimize flip-flop usage.

In general, this means plugins can simply produce and consume pipeline register
values without having to worry about connecting all stages involved in the
propagation.

### Arbitration

The pipeline scheduling logic is responsible for resolving all data hazards. In
order to do this, it needs information about when stages need certain register
values. It also provides information to the stages about, for example, if they
are currently allowed to execute.

The communication between the scheduling logic and the stages is facilitated by
the `Arbitration` class defined in `Stage.scala`. The most important signals are
the following (I/O direction from the perspective of `Stage`, all signals are of
type `Bool`):

- `isValid` (input): is the instruction currently in this stage valid (i.e.,
  does it eventually need to be executed);
- `isStalled` (input): is this stage stalled due to external factors (e.g.,
  waiting for a register value);
- `isReady` (output): is this stage done executing the current instruction (used
  to implement multi-cycle logic in stages);
- `rs1Needed`/`rs2Needed` (output): does this stage need the value of the
  `RS1_DATA`/`RS2_DATA` pipeline registers. Used to signal to the scheduling
  logic that register values are needed in this cycle and that these values
  should be forwarded or the pipeline stalled;

Every stage has its own instantiation of `Arbitration` called `arbitration`
which can be used by plugins. In the generated Verilog code, the signals are
therefore called, for example, `arbitration_isValid`.

## Pipeline

`Pipeline` is a trait that is implemented by the classes that build the pipeline
structure. The current implementors are `StaticPipeline` (in-order static
pipeline) and `DynamicPipeline` (out-of-order pipeline, work in progress). Most
plugins, including those used in this project, do not need to be aware of the
underlying pipeline structure and only use the generic `Pipeline` trait.

The full definition of this trait can be found in `Pipeline.scala`, its most
imported methods are listed here:

- `config`: returns the `Config` object of the `Pipeline`. This object contains
  global configuration, most importantly `xlen` which is the bit-width of the
  processor being built (see `Config.scala`);
- `data`: returns the `StandardPipelineData` object containing the predefined
  [`PipelineData` objects](#pipelinedata) (see `PipelineData.scala`);
- `service[T]`: returns the [service](#services) of type `T`.

## Plugins

As mentioned before, all logic in stages as well as in the pipeline is created
by plugins. A plugin is implemented by a class inheriting the `Plugin` class.
Plugins can override three methods to implement their logic:

- `setup`: used to perform any kind of configuration. Most often used to
  configure services offered by other plugins;
- `build`: used to build any logic (called after `setup` has been called on all
  plugins);
- `finish`: used for any actions that should be performed after all logic was
  built (called after `build` has been called on all plugins).

Plugins have access to the `Pipeline` and `Config` objects through the
`pipeline` and `config` methods, respectively.

Plugins can use the `plug` method to add logic to stages. Most often, logic is
added as an
[`Area`](https://spinalhdl.github.io/SpinalDoc-RTD/master/SpinalHDL/Structuring/area.html).
When doing this, the `Area` will automatically be named as the plugin class so
that all added signals are prefixed with this name.

A typical plugins looks something like this:
```scala
// Plugin[Pipeline] means we don't need to know the
// pipeline structure
class SomePlugin(stage: Stage) extends Plugin[Pipeline] {
  override def setup(): Unit = {
    // Configure services
  }
  override def build(): Unit = {
    stage plug new Area {
      // Allow to use methods of stage directly
      import stage._
      // Create logic
      // For example, this will be named
      // SomePlugin_someBool in Verilog
      val someBool = Bool
    }
  }
}
```

In this example, the plugin only adds logic to a single stage which is provided
as a constructor argument. By providing more arguments, plugins can be created
that add logic to multiple stages. For example, the `RegisterFile` plugin adds
register read logic to one stage and write logic to another.

## Services

Services are traits that can be implemented by plugins and used by other
plugins. Currently, all service traits are defined in `Services.scala`. The
`getService` method defined in the `Pipeline` trait can be used to get access to
the plugin that implements a certain trait. The rest of this section will
describe some of the most important services.

### DecoderService

The `DecoderService` trait is implemented by the `Decoder` plugin in
`Decoder.scala`. This trait allows plugins to add decoding logic to the decode
stage which can be used to implement new instructions. Decodings are specified
using the following parameters:

- `opcode`
  ([`MaskedLiteral`](https://spinalhdl.github.io/SpinalDoc-RTD/master/SpinalHDL/Data%20types/bits.html#maskedliteral)):
  bitmask that is matched against the full 32-bit instruction register. When it
  matches, the following actions are applied;
- `itype` (`InstructionType`, see `RiscV.scala`): specifies which instruction
  type should be used for decoding. This will ensure that the `RS1`, `RS2`,
  `RD`, and `IMM` pipeline registers are automatically decoded;
- `action` (`Map[PipelineData, Data]`): mapping from pipeline registers to the
  value that should be stored in them whenever an instruction matches `opcode`.

To specify a decoding, the `configure` method should be called on a
`DecoderService`. This gives access to a `DecoderConfig` object on which the
`addDecoding` method can be called. It also offers a `addDefault` method to
specify default values for pipeline registers.

As an example, we show the relevant parts of the `ecall` instruction
implementation (see `MachineMode.scala` for the full details). The basic idea is
to define a new pipeline register called `ECALL` which is set to `True` whenever
the `ecall` opcode is detected. Then, inside `build`, we add logic that is
triggered when the `ECALL` pipeline register is asserted:

```scala
class MachineMode(stage: Stage) extends Plugin[Pipeline] {
  object Data {
    object ECALL extends PipelineData(Bool())
  }
  object Opcodes {
    val ECALL = M"00000000000000000000000001110011"
  }
  override def setup(): Unit = {
    pipeline.getService[DecoderService].configure {config =>
      config.addDefault(Map(Data.ECALL -> False))
      config.addDecoding(Opcodes.ECALL, InstructionType.I,
                         Map(Data.ECALL -> True))
    }
  }
  override def build(): Unit = {
    stage plug new Area {
      import stage._
      when (arbitration.isValid) {
        when (value(Data.ECALL)) {
          // Instruction logic
        }
      }
    }
  }
}
```

### IntAluService

Certain instructions need to perform arithmetic operations as part of their
functionality. To prevent needing multiple hardware instantiations of (often
expensive) arithmetic circuits, the `IntAluService` trait offers a way for
plugins to request the `ALU` plugin to perform operations on their behalf. To
this end, it provides the `addOperation` method which allows a plugin to specify
an opcode which the `ALU` should recognize, which operation should be performed,
and what the left- and right-hand sides should be. The result of the  arithmetic
operation is stored in the pipeline register identified by the `PipelineData`
object returned by the `resultData` method.

As an example, the `jal` instruction performs a program-counter-relative jump
specified by an immediate offset. Hence, the target address is the sum of the
program counter and the immediate encoded in the instruction. This is the
relevant code in the `BranchUnit` plugin (see `BranchUnit.scala`):

```scala
override def setup(): Unit = {
  val alu = pipeline.getService[IntAluService]
  alu.addOperation(Opcodes.JAL, alu.AluOp.ADD,
                   alu.Src1Select.PC,
                   alu.Src2Select.IMM)
  ...
}
override def build(): Unit = {
  stage plug new Area {
    import stage._

    val alu = pipeline.getService[IntAluService]
    val target = value(alu.resultData)
    ...
  }
}
```

### JumpService

The `JumpService` trait offers the functionality to make the pipeline perform a
jump. Its `jump` method takes the `Stage` that performs the jump and the target
address as argument.

## Debugging tips

We will conclude this section by providing some tips of how to interpret the
`VCD` file generated by simulating the processor. To easily visualize what
happens in each stage, it is best to always show a few common signals of all of
them. Use the following as a starting point:

- `in_PC`: the program counter of the current instruction in the stage;
- `in_IR`: the instruction register. A helper script is provided
  (`Tools/disas.py`) to automatically disassemble this signal. It can be used by
  right-clicking on the signal in GTKWave and going to "Data Format" ->
  "Translate Filter Process" -> "Enable and Select". Make sure the RISC-V
  toolchain is in your `PATH` when using this script;
- `arbitration_isValid`: indicates when the current instruction is valid.

Multiple signals can be grouped by selecting them and pressing "G". It is useful
to group all signals belonging to the same stage.

# Assignment

For this project, you will be implementing a processor extension to protect
against return address smashing attacks. The idea is simple: whenever a function
call is made, the return address is encrypted. Before returning from a function,
the return address is decrypted again.

The extension will be implemented in two steps. First, the encryption and
decryption functionality is added while using a hard-coded key. Then, a new
instruction should be implemented to dynamically set the key from software. But
before creating this return address  smashing defence, you are asked to create a
proof-of-concept attack.

## Exploiting a buffer overflow on RISC-V

All files for this part of the assignment are in the `Exploit` subdirectory. The
file `smash.c` contains a function that reads a string from the standard input
and then prints the hexadecimal ASCII values of all characters to the standard
output:

```c
void smash_this()
{
    char buf[128] = {0,};
    gets(buf);

    printf("stdin: ");

    for (size_t i = 0; buf[i] != 0; ++i)
        printf("%02x ", buf[i]);

    printf("\n");
}
```

Since `gets` stores all input from the standard input until the next newline
into the destination buffer, this function is clearly vulnerable to a buffer
overflow attack.

> **Task 1:** Craft a payload that, when provided as the standard input of the
> exploitable program, prints the string "p0wned!" to the standard output.

Some hints (which you do not have to follow):

- Embed the string in your payload and call `puts` with a pointer to this
  string;
- Run the program in the simulator and use GTKWave to find the address of the
  stack pointer when entering the `smash_this` function. This will give you the
  address of `buf`;
- Certain addresses (e.g., `puts`) need to be hard-coded;
- Make sure the only `0x0a` (newline) byte in your payload is at the very end.

The `Exploit` directory contains a Makefile to build both the main program and
the exploit payload. After running `make`, the files `smash.bin` and
`smash.ihex` can be run in the simulator. The standard input of the simulator
will be attached to the standard input of the program running in the simulator.
Therefore, the program can be run as follows:
```
$ echo 'Hello' ../RiscV/sim/build/sim smash.bin
stdin: 48 65 6c 6c 6f
```

The payload should be implemented in `shellcode.s`. The Makefile compiles this
file into `shellcode.bin` which can be used to inject the payload into the
program. For this part of the assignment, only `shellcode.s` needs to be changed
and committed to your repository.

## Encrypting and decrypting return addresses

To be able to encrypt and decrypt return addresses, we have to identify when
function calls and returns are made. Unfortunately, RISC-V does not define
dedicated instructions for calls and returns and instead uses unconditional
jumps in both cases. This means we need a heuristic to distinguish calls and
return from normal unconditional jumps.

All unconditional jump instructions in RISC-V store the return address in the
destination register. The [RISC-V calling
convention](https://github.com/riscv-non-isa/riscv-elf-psabi-doc/blob/master/riscv-cc.adoc)
specifies the use of the `x1` (`ra`) register for the return address of function
calls. Therefore, unconditional jump instructions that store their return
address in `x1` can be considered function calls. Try to find a similar
heuristic for identifying function returns (hint: look at the assembly generated
by GCC).

For the jumps that are identified as calls, their return address should be
encrypted before being stored in their destination register. Similarly, for
returns, the target address should be decrypted before jumping to it. The goal
of this project is not to implement cryptographic primitives so a component
called `CryptoUnit` is provided for this. This component implements both
encryption and decryption functionality in a single cycle (i.e., as purely
combinational logic) and has the following I/O ports:

- `key`: input (`UInt(32 bits)`): The key to be used for encryption/decryption;
- `value`: input (`UInt(32 bits)`): The value to be encrypted/decrypted;
- `operation`: input (`CryptoUnit.Operation`): The operation (`ENCRYPT` or
  `DECRYPT`) to be performed;
- `result`: output (`UInt(32 bits)`): The encrypted/decrypted value.

> **Task 2:** Add logic to the `BranchUnit` plugin for encrypting and decrypting
> return addresses. Use a single instantiation of the `CryptoUnit` component for
> the cryptographic operations. The key to be used for encrypting and decrypting
> values should be hard-coded.

The implementation should be made inside the `Proteus` directory. In principle,
the only code that needs to be changed is that of the `BranchUnit` plugin in
`src/main/scala/riscv/plugins/BranchUnit.scala`.

## Setting the key dynamically

To be able to set the key used for encrypting return addresses from software, we
need to add a new instruction. The RISC-V unprivileged ISA
[specification](https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMAFDQC/riscv-spec-20191213.pdf)
dedicates a full chapter (Chapter 26) to extending RISC-V. For our current
purposes, however, Table 24.1 on page 129 contains all necessary information.
Every cell in this table marked with "custom-i" may be used to encode custom
instructions.

The new instruction needs the 32-bit key as input and has no output value. This
means the R-type encoding can be used while ignoring the `rs2` and `rd` fields
(which means setting them to fixed values).

The default value for the key should be zero and this should be interpreted as
disabling the encryption and decryption of return addresses.

> **Task 3:** Implement a new instruction that reads a key from `rs1` and makes
> sure that key is used for any subsequent encryptions and decryptions of return
> addresses. When the key is set to zero, the return address protection feature
> is disabled.

As with the previous task, the implementation of the new instruction can be done
by modifying the `BranchUnit` plugin. Make sure the changes to this file are
committed to your repository.

# Practicalities

## Questions

Questions can be asked via the [issue
tracker](https://gitlab.kuleuven.be/distrinet/education/capita-selecta-secure-software/extending-processors-for-security/project/-/issues).

## Submission

The deadline will be announced as soon as possible.

A private repository will be created for everyone which must be used for
submission. At the time of the deadline, the repository will be archived (which
means it will be read-only) and the state of the repository at that time will be
considered your submission.

Make sure you have committed the following files to your repository:
- Task 1: `Exploit/shellcode.s`;
- Task 2 and 3: `Proteus/src/main/scala/riscv/plugins/BranchUnit.scala`;
- Short explanation of your solutions (maximum 2 pages): `report.pdf`.

After the submission, there will be an oral defence where you will be asked to
explain your solution. The practical information about the defences will be
announced through Toledo.
