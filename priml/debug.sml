val verbose = ref true

fun verb f = if !verbose then f () else ()

fun verbprint s = if !verbose then print s else ()
