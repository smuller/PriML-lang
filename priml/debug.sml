val verbose = ref false

fun verb f = if !verbose then f () else ()

fun verbprint s = if !verbose then print s else ()
