"use strict"

class FFT {
    constructor(size) {
        this.size = size | 0;
        if (this.size <= 1 || (this.size & (this.size - 1)) !== 0)
            throw new Error('FFT size must be a power of two and bigger than 1');

        this._csize = size << 1;

        // NOTE: Use of `var` is intentional for old V8 versions
        var table = new Array(this.size * 2);
        for (var i = 0; i < table.length; i += 2) {
            const angle = Math.PI * i / this.size;
            table[i] = Math.cos(angle);
            table[i + 1] = -Math.sin(angle);
        }
        this.table = table;

        // Find size's power of two
        var power = 0;
        for (var t = 1; this.size > t; t <<= 1)
            power++;

        // Calculate initial step's width:
        //   * If we are full radix-4 - it is 2x smaller to give initial len=8
        //   * Otherwise it is the same as `power` to give len=4
        this._width = power % 2 === 0 ? power - 1 : power;

        // Pre-compute bit-reversal patterns
        this._bitrev = new Array(1 << this._width);
        for (var j = 0; j < this._bitrev.length; j++) {
            this._bitrev[j] = 0;
            for (var shift = 0; shift < this._width; shift += 2) {
                var revShift = this._width - shift - 2;
                this._bitrev[j] |= ((j >>> shift) & 3) << revShift;
            }
        }

        this._out = null;
        this._data = null;
        this._inv = 0;
    }
}

function fft_fromComplexArray(complex, storage) {
    var res = storage || new Array(complex.length >>> 1);
    for (var i = 0; i < complex.length; i += 2)
        res[i >>> 1] = complex[i];
    return res;
};

function fft_createComplexArray(fft) {
    const res = new Array(fft._csize);
    for (var i = 0; i < res.length; i++)
        res[i] = 0;
    return res;
};

function fft_toComplexArray(fft, input, storage) {
    var res = storage || createComplexArray(fft);
    for (var i = 0; i < res.length; i += 2) {
        res[i] = input[i >>> 1];
        res[i + 1] = 0;
    }
    return res;
};

function fft_completeSpectrum(fft, spectrum) {
    var size = fft._csize;
    var half = size >>> 1;
    for (var i = 2; i < half; i += 2) {
        spectrum[size - i] = spectrum[i];
        spectrum[size - i + 1] = -spectrum[i + 1];
    }
};

function fft_transform(fft, out, data) {
    if (out === data)
        throw new Error('Input and output buffers must be different');

    fft._out = out;
    fft._data = data;
    fft._inv = 0;
    _fft_transform4(fft);
    fft._out = null;
    fft._data = null;
};

function fft_realTransform(fft, out, data) {
    if (out === data)
        throw new Error('Input and output buffers must be different');

    fft._out = out;
    fft._data = data;
    fft._inv = 0;
    _fft_realTransform4(fft);
    fft._out = null;
    fft._data = null;
};

function fft_inverseTransform(fft, out, data) {
    if (out === data)
        throw new Error('Input and output buffers must be different');

    fft._out = out;
    fft._data = data;
    fft._inv = 1;
    _fft_transform4(fft);
    for (var i = 0; i < out.length; i++)
        out[i] /= fft.size;
    fft._out = null;
    fft._data = null;
};

// Radix-4 implementation
//
// NOTE: Uses of `var` are intentional for older V8 version that do not
// support both `let compound assignments` and `const phi`
function _fft_transform4(fft) {
    var out = fft._out;
    var size = fft._csize;

    // Initial step (permute and transform)
    var width = fft._width;
    var step = 1 << width;
    var len = (size / step) << 1;

    var outOff;
    var t;
    var bitrev = fft._bitrev;
    if (len === 4) {
        for (outOff = 0, t = 0; outOff < size; outOff += len, t++) {
            const off = bitrev[t];
            _fft_singleTransform2(fft, outOff, off, step);
        }
    } else {
        // len === 8
        for (outOff = 0, t = 0; outOff < size; outOff += len, t++) {
            const off = bitrev[t];
            _fft_singleTransform4(fft, outOff, off, step);
        }
    }

    // Loop through steps in decreasing order
    var inv = fft._inv ? -1 : 1;
    var table = fft.table;
    for (step >>= 2; step >= 2; step >>= 2) {
        len = (size / step) << 1;
        var quarterLen = len >>> 2;

        // Loop through offsets in the data
        for (outOff = 0; outOff < size; outOff += len) {
            // Full case
            var limit = outOff + quarterLen;
            for (var i = outOff, k = 0; i < limit; i += 2, k += step) {
                const A = i;
                const B = A + quarterLen;
                const C = B + quarterLen;
                const D = C + quarterLen;

                // Original values
                const Ar = out[A];
                const Ai = out[A + 1];
                const Br = out[B];
                const Bi = out[B + 1];
                const Cr = out[C];
                const Ci = out[C + 1];
                const Dr = out[D];
                const Di = out[D + 1];

                // Middle values
                const MAr = Ar;
                const MAi = Ai;

                const tableBr = table[k];
                const tableBi = inv * table[k + 1];
                const MBr = Br * tableBr - Bi * tableBi;
                const MBi = Br * tableBi + Bi * tableBr;

                const tableCr = table[2 * k];
                const tableCi = inv * table[2 * k + 1];
                const MCr = Cr * tableCr - Ci * tableCi;
                const MCi = Cr * tableCi + Ci * tableCr;

                const tableDr = table[3 * k];
                const tableDi = inv * table[3 * k + 1];
                const MDr = Dr * tableDr - Di * tableDi;
                const MDi = Dr * tableDi + Di * tableDr;

                // Pre-Final values
                const T0r = MAr + MCr;
                const T0i = MAi + MCi;
                const T1r = MAr - MCr;
                const T1i = MAi - MCi;
                const T2r = MBr + MDr;
                const T2i = MBi + MDi;
                const T3r = inv * (MBr - MDr);
                const T3i = inv * (MBi - MDi);

                // Final values
                const FAr = T0r + T2r;
                const FAi = T0i + T2i;

                const FCr = T0r - T2r;
                const FCi = T0i - T2i;

                const FBr = T1r + T3i;
                const FBi = T1i - T3r;

                const FDr = T1r - T3i;
                const FDi = T1i + T3r;

                out[A] = FAr;
                out[A + 1] = FAi;
                out[B] = FBr;
                out[B + 1] = FBi;
                out[C] = FCr;
                out[C + 1] = FCi;
                out[D] = FDr;
                out[D + 1] = FDi;
            }
        }
    }
};

// radix-2 implementation
//
// NOTE: Only called for len=4
function _fft_singleTransform2(fft, outOff, off, step) {
    const out = fft._out;
    const data = fft._data;

    const evenR = data[off];
    const evenI = data[off + 1];
    const oddR = data[off + step];
    const oddI = data[off + step + 1];

    const leftR = evenR + oddR;
    const leftI = evenI + oddI;
    const rightR = evenR - oddR;
    const rightI = evenI - oddI;

    out[outOff] = leftR;
    out[outOff + 1] = leftI;
    out[outOff + 2] = rightR;
    out[outOff + 3] = rightI;
};

// radix-4
//
// NOTE: Only called for len=8
function _fft_singleTransform4(fft, outOff, off,
    step) {
    const out = fft._out;
    const data = fft._data;
    const inv = fft._inv ? -1 : 1;
    const step2 = step * 2;
    const step3 = step * 3;

    // Original values
    const Ar = data[off];
    const Ai = data[off + 1];
    const Br = data[off + step];
    const Bi = data[off + step + 1];
    const Cr = data[off + step2];
    const Ci = data[off + step2 + 1];
    const Dr = data[off + step3];
    const Di = data[off + step3 + 1];

    // Pre-Final values
    const T0r = Ar + Cr;
    const T0i = Ai + Ci;
    const T1r = Ar - Cr;
    const T1i = Ai - Ci;
    const T2r = Br + Dr;
    const T2i = Bi + Di;
    const T3r = inv * (Br - Dr);
    const T3i = inv * (Bi - Di);

    // Final values
    const FAr = T0r + T2r;
    const FAi = T0i + T2i;

    const FBr = T1r + T3i;
    const FBi = T1i - T3r;

    const FCr = T0r - T2r;
    const FCi = T0i - T2i;

    const FDr = T1r - T3i;
    const FDi = T1i + T3r;

    out[outOff] = FAr;
    out[outOff + 1] = FAi;
    out[outOff + 2] = FBr;
    out[outOff + 3] = FBi;
    out[outOff + 4] = FCr;
    out[outOff + 5] = FCi;
    out[outOff + 6] = FDr;
    out[outOff + 7] = FDi;
};

// Real input radix-4 implementation
function _fft_realTransform4(fft) {
    var out = fft._out;
    var size = fft._csize;

    // Initial step (permute and transform)
    var width = fft._width;
    var step = 1 << width;
    var len = (size / step) << 1;

    var outOff;
    var t;
    var bitrev = fft._bitrev;
    if (len === 4) {
        for (outOff = 0, t = 0; outOff < size; outOff += len, t++) {
            const off = bitrev[t];
            _fft_singleRealTransform2(fft, outOff, off >>> 1, step >>> 1);
        }
    } else {
        // len === 8
        for (outOff = 0, t = 0; outOff < size; outOff += len, t++) {
            const off = bitrev[t];
            _fft_singleRealTransform4(fft, outOff, off >>> 1, step >>> 1);
        }
    }

    // Loop through steps in decreasing order
    var inv = fft._inv ? -1 : 1;
    var table = fft.table;
    for (step >>= 2; step >= 2; step >>= 2) {
        len = (size / step) << 1;
        var halfLen = len >>> 1;
        var quarterLen = halfLen >>> 1;
        var hquarterLen = quarterLen >>> 1;
        // Loop through offsets in the data
        for (outOff = 0; outOff < size; outOff += len) {
            // Full case
            var limit = outOff + quarterLen;
            for (var i = outOff, k = 0; i < limit; i += 2, k += step) {
                const A = i;
                const B = A + quarterLen;
                const C = B + quarterLen;
                const D = C + quarterLen;

                // Original values
                const Ar = out[A];
                const Ai = out[A + 1];
                const Br = out[B];
                const Bi = out[B + 1];
                const Cr = out[C];
                const Ci = out[C + 1];
                const Dr = out[D];
                const Di = out[D + 1];

                // Middle values
                const MAr = Ar;
                const MAi = Ai;

                const tableBr = table[k];
                const tableBi = inv * table[k + 1];
                const MBr = Br * tableBr - Bi * tableBi;
                const MBi = Br * tableBi + Bi * tableBr;

                const tableCr = table[2 * k];
                const tableCi = inv * table[2 * k + 1];
                const MCr = Cr * tableCr - Ci * tableCi;
                const MCi = Cr * tableCi + Ci * tableCr;

                const tableDr = table[3 * k];
                const tableDi = inv * table[3 * k + 1];
                const MDr = Dr * tableDr - Di * tableDi;
                const MDi = Dr * tableDi + Di * tableDr;

                // Pre-Final values
                const T0r = MAr + MCr;
                const T0i = MAi + MCi;
                const T1r = MAr - MCr;
                const T1i = MAi - MCi;
                const T2r = MBr + MDr;
                const T2i = MBi + MDi;
                const T3r = inv * (MBr - MDr);
                const T3i = inv * (MBi - MDi);

                // Final values
                const FAr = T0r + T2r;
                const FAi = T0i + T2i;

                const FCr = T0r - T2r;
                const FCi = T0i - T2i;

                const FBr = T1r + T3i;
                const FBi = T1i - T3r;

                const FDr = T1r - T3i;
                const FDi = T1i + T3r;

                out[A] = FAr;
                out[A + 1] = FAi;
                out[B] = FBr;
                out[B + 1] = FBi;
                out[C] = FCr;
                out[C + 1] = FCi;
                out[D] = FDr;
                out[D + 1] = FDi;
            }
        }
    }
};

// radix-2 implementation
//
// NOTE: Only called for len=4
function _fft_singleRealTransform2(fft, outOff,
    off,
    step) {
    const out = fft._out;
    const data = fft._data;

    const evenR = data[off];
    const oddR = data[off + step];

    const leftR = evenR + oddR;
    const rightR = evenR - oddR;

    out[outOff] = leftR;
    out[outOff + 1] = 0;
    out[outOff + 2] = rightR;
    out[outOff + 3] = 0;
};

// radix-4
//
// NOTE: Only called for len=8
function _fft_singleRealTransform4(fft, outOff,
    off,
    step) {
    const out = fft._out;
    const data = fft._data;
    const inv = fft._inv ? -1 : 1;
    const step2 = step * 2;
    const step3 = step * 3;

    // Original values
    const Ar = data[off];
    const Br = data[off + step];
    const Cr = data[off + step2];
    const Dr = data[off + step3];

    // Pre-Final values
    const T0r = Ar + Cr;
    const T1r = Ar - Cr;
    const T2r = Br + Dr;
    const T3r = inv * (Br - Dr);

    // Final values
    const FAr = T0r + T2r;

    const FBr = T1r;
    const FBi = -T3r;

    const FCr = T0r - T2r;

    const FDr = T1r;
    const FDi = T3r;

    out[outOff] = FAr;
    out[outOff + 1] = 0;
    out[outOff + 2] = FBr;
    out[outOff + 3] = FBi;
    out[outOff + 4] = FCr;
    out[outOff + 5] = 0;
    out[outOff + 6] = FDr;
    out[outOff + 7] = FDi;
}

export function makeFFT(size) {
    return new FFT(size);
}

export function fftSize(fft) {
    return fft.size;
}

export function fromComplexArray(complexArray) {
    return fft_fromComplexArray(complexArray);
}

export function createComplexArray(fft) {
    return fft_createComplexArray(fft);
}

export function toComplexArray(fft) {
    return function(realInput) {
        return fft_toComplexArray(fft, realInput);
    };
}

export function transform(fft) {
    return function(data) {
        var out = fft_createComplexArray(fft);
        fft_transform(fft, out, data);
        return out;
    };
}

export function realTransform(fft) {
    return function(data) {
        var out = fft_createComplexArray(fft);
        fft_realTransform(fft, out, data);
        return out;
    };
}

export function inverseTransform(fft) {
    return function(data) {
        var out = fft_createComplexArray(fft);
        fft_inverseTransform(fft, out, data);
        return out;
    };
}

// Mutable functions

export function fromComplexArrayST(complexArray) {
    return function(storage) {
        return function() {
            return fft_fromComplexArray(complexArray, storage);
        };
    };
}

export function toComplexArrayST(fft) {
    return function(realInput) {
        return function() {
            return fft_toComplexArray(fft, realInput);
        }
    };
}

export function transformST(fft) {
    return function(data) {
        return function(out) {
            return function() {
                fft_transform(fft, out, data);
            };
        };
    };
}

export function realTransformST(fft) {
    return function(data) {
        return function(out) {
            return function() {
                fft_realTransform(fft, out, data);
            };
        };
    };
}

export function inverseTransformST(fft) {
    return function(data) {
        return function(out) {
            return function() {
                fft_inverseTransform(fft, out, data);
            };
        };
    };
}

export function completeSpectrum(fft) {
    return function(spectrum) {
        return function() {
            fft_completeSpectrum(fft, spectrum);
        };
    };
}
