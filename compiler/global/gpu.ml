(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(** The type of the function :

      Undefined : don't know
      No_constraint : normal functions
      GPU : contains a pmap or a function of type GPU
      Kernel : a kernel created by split_kernel with only sequential operations
      Parallel_kernel : a kernel created by split_kernel with either a map or a pmap in it
      Kernel_caller : the CPU side of a node with the keyword kernel
      CPU : calls a Kernel_caller function or a CPU function *)
type gpu =
  | Undefined
  | No_constraint
  (* The integer is the number of dimensions already taken for parallelism. *)
  | GPU of int
  (* The maximum number of the GPU functions called or 0. *)
  | Kernel of int
  (* The list of sizes for parallelization and the integer of the GPU called (0 if a pmap). *)
  | Parallel_kernel of int list * int
  | Kernel_caller
  | CPU

(** The memory location of a variable :
      Private : stack-allocated on the CPU, in the registers of a work-item on the GPU
      Local : OpenCL local memory, equivalent of CUDA shared memory
      Global : OpenCL global memory on the GPU, an OpenCL buffer on the CPU *)
type mem_loc =
  | Private
  | Local
  | Global
