// IGNORE_BACKEND: WASM

// FILE: test.kt
fun box() {
    var i = 0
    ++i
    i += 1
    i +=
        1
    i -= 1
    i -=
        1
    i = i + 1
    i =
        i + 1
    i =
        i +
            1
}

// EXPECTATIONS JVM_IR
// test.kt:5 box
// test.kt:6 box
// test.kt:7 box
// test.kt:8 box
// test.kt:9 box
// test.kt:8 box
// test.kt:10 box
// test.kt:11 box
// test.kt:12 box
// test.kt:11 box
// test.kt:13 box
// test.kt:15 box
// test.kt:14 box
// test.kt:17 box
// test.kt:18 box
// test.kt:17 box
// test.kt:16 box
// test.kt:19 box

// EXPECTATIONS JS_IR
// test.kt:5 box
// test.kt:6 box
// test.kt:7 box
// test.kt:8 box
// test.kt:10 box
// test.kt:11 box
// test.kt:13 box
// test.kt:15 box
// test.kt:17 box
// test.kt:19 box
