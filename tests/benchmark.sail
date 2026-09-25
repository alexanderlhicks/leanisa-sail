val benchmark_start = impure "benchmark_start" : unit -> unit
val benchmark_stop = impure "benchmark_stop" : string -> unit

function main() -> unit = {
  let mem : vector(65536, eword) = vector_init(65536, sail_zeros(192));
  benchmark_start();
  let index = build_address_index(65536);
  benchmark_stop("prepare_65536");
  let positions : vector(3, bits(64)) = [0x000000000000ffff, 0x0000000000007fff, 0x000000000000001f];
  let reference_labels : vector(3, string) = ["scan_65535", "scan_32767", "scan_31"];
  let indexed_labels : vector(3, string) = ["indexed_65535", "indexed_32767", "indexed_31"];
  foreach (j from 0 to 2) {
    let address = gpow(positions[j]);
    benchmark_start();
    foreach (i from 0 to 63) {
      assert(read_memory(mem, address).valid, "reference lookup");
    };
    benchmark_stop(reference_labels[j]);
    benchmark_start();
    foreach (i from 0 to 63) {
      assert(read_memory_indexed(mem, index, address).valid, "indexed lookup");
    };
    benchmark_stop(indexed_labels[j]);
  };
  let instruction = Set(gpow(0x000000000000ffff), sail_zeros(192));
  let small : vector(128, instruction) = vector_init(128, instruction);
  let large : vector(2048, instruction) = vector_init(2048, instruction);
  let local : vector(32, instruction) = vector_init(32, Set(0x0000000000000004, sail_zeros(192)));
  benchmark_start();
  assert(run(local, mem, sail_zeros(256), 31).verdict == Halted, "reference low-address run");
  benchmark_stop("run_scan_32_low");
  benchmark_start();
  assert(run_indexed(local, mem, sail_zeros(256), 31).verdict == Halted, "indexed low-address run");
  benchmark_stop("run_indexed_32_low");
  benchmark_start();
  assert(run(small, mem, sail_zeros(256), 127).verdict == Halted, "reference small run");
  benchmark_stop("run_scan_128");
  benchmark_start();
  assert(run_indexed(small, mem, sail_zeros(256), 127).verdict == Halted, "indexed small run");
  benchmark_stop("run_indexed_128");
  benchmark_start();
  assert(run(large, mem, sail_zeros(256), 2047).verdict == Halted, "reference large run");
  benchmark_stop("run_scan_2048");
  benchmark_start();
  assert(run_indexed(large, mem, sail_zeros(256), 2047).verdict == Halted, "indexed large run");
  benchmark_stop("run_indexed_2048");
}
