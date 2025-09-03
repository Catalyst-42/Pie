use std::error::Error;
use std::thread::sleep;
use std::time::{Duration, Instant};

static mut MODULO: i64 = 0;
static mut INVERSE_MODULO: f64 = 0.0;

fn initialize_modulo(m: i64) {
    unsafe {
        MODULO = m;
        INVERSE_MODULO = 1.0 / m as f64;
    }
}

fn mul_mod(a: i64, b: i64) -> i64 {
    unsafe {
        let q = (INVERSE_MODULO * a as f64 * b as f64) as i64;
        a * b - q * MODULO
    }
}

fn sum_mul_mod(a: i64, b: i64, c: i64, d: i64) -> i64 {
    unsafe {
        let q = (INVERSE_MODULO * (a as f64 * b as f64 + c as f64 * d as f64)) as i64;
        a * b + c * d - q * MODULO
    }
}

fn easy_round(x: f64) -> f64 {
    let full_double = 2f64.powi(53);
    let y = x + full_double;
    y - full_double
}

fn extended_gcd(a: i64) -> (i64, i64) {
    let mut a0 = 1;
    let mut a1 = 0;
    let mut r0 = a;
    let mut r1 = unsafe { MODULO };

    while r1 > 0 {
        let q = r0 / r1;
        (a0, a1) = (a1, a0 - q * a1);
        (r0, r1) = (r1, r0 - q * r1);
    }
    (r0, a0)
}

fn inv_mod(a: i64) -> i64 {
    let a = a % unsafe { MODULO };
    let a = if a < 0 { a + unsafe { MODULO } } else { a };
    let (gcd, a_out) = extended_gcd(a);

    if gcd != 1 {
        panic!("Error, gcd should be 1");
    }
    a_out
}

fn pow_mod(a: i64, b: i64) -> i64 {
    let mut r = 1;
    let mut a = a;
    let mut b = b;

    while b > 0 {
        if b & 1 == 1 {
            r = mul_mod(r, a);
        }
        b >>= 1;
        if b == 0 {
            break;
        }
        a = mul_mod(a, a);
    }
    r
}

fn sum_binomial_mod(n: i64, k: i64) -> i64 {
    if k > n / 2 {
        let mut s = pow_mod(2, n) - sum_binomial_mod(n, n - k - 1);
        if s < 0 {
            s += unsafe { MODULO };
        }
        return s;
    }

    let mut prime_factors = vec![];
    let mut mm = unsafe { MODULO };
    let sqrt_mm = (mm as f64).sqrt() as i64;
    for p in (3..=sqrt_mm).step_by(2) {
        if mm % p == 0 {
            mm /= p;
            if p <= k {
                prime_factors.push(p);
            }
            while mm % p == 0 {
                mm /= p;
            }
        }
    }
    if mm > 1 && mm <= k {
        prime_factors.push(mm);
    }

    let mut binomial_powers = vec![1; prime_factors.len()];
    let mut next_denom: Vec<i64> = prime_factors.iter().map(|&p| p).collect();
    let mut next_num: Vec<i64> = prime_factors.iter().map(|&p| p * (n / p)).collect();
    let mut binomial_num0 = 1;
    let mut binomial_denom = 1;
    let mut sum_num = 1;
    let mut binomial_secondary = 1;

    for j in 1..=k {
        let mut binomial_secondary_update = false;
        let mut num = n - j + 1;
        let mut denom = j;

        for (i, &p) in prime_factors.iter().enumerate() {
            if next_num[i] == n - j + 1 {
                binomial_secondary_update = true;
                next_num[i] -= p;
                binomial_powers[i] *= p;
                num /= p;
                while num % p == 0 {
                    binomial_powers[i] *= p;
                    num /= p;
                }
            }
            if next_denom[i] == j {
                binomial_secondary_update = true;
                next_denom[i] += p;
                binomial_powers[i] /= p;
                denom /= p;
                while denom % p == 0 {
                    binomial_powers[i] /= p;
                    denom /= p;
                }
            }
        }

        if binomial_secondary_update {
            binomial_secondary = 1;
            for &binomial_power in &binomial_powers {
                binomial_secondary = mul_mod(binomial_secondary, binomial_power);
            }
        }

        binomial_num0 = mul_mod(binomial_num0, num);
        binomial_denom = mul_mod(binomial_denom, denom);

        if binomial_secondary != 1 {
            sum_num = sum_mul_mod(sum_num, denom, binomial_num0, binomial_secondary);
        } else {
            sum_num = mul_mod(sum_num, denom) + binomial_num0;
        }
    }

    sum_num = mul_mod(sum_num, inv_mod(binomial_denom));
    sum_num
}

fn digits_of_fraction(n: i64, a: i64, b: i64) -> f64 {
    initialize_modulo(b);
    let power = pow_mod(10, n);
    let c = mul_mod(power, a);
    c as f64 / b as f64
}

fn digits_of_series(n: i64, m: i64) -> f64 {
    let mut x = 0.0;
    for k in (0..m).step_by(2) {
        x += digits_of_fraction(n, 4, 2 * k + 1) - digits_of_fraction(n, 4, 2 * k + 3);
        x -= easy_round(x);
    }
    x
}

fn digits_of_pi(n: i64) -> f64 {
    let logn = (n as f64).ln();
    let m = 2 * ((3.0 * n as f64 / logn / logn / logn) as i64);
    let n_float = n as f64;
    let n_calc = 1 + ((n_float + 15.0) * 10.0_f64.ln() / (1.0 + (2.0 * m as f64).ln())) as i64;
    let n_calc = n_calc + (n_calc % 2);
    let m_max = m * n_calc + n_calc;

    let mut x = digits_of_series(n, m_max);

    for k in 0..n_calc {
        let m = 2 * m * n_calc + 2 * k + 1;
        initialize_modulo(m);
        let mut s = sum_binomial_mod(n_calc, k);
        s = mul_mod(s, pow_mod(5, n_calc));
        s = mul_mod(s, pow_mod(10, n - n_calc));
        s = mul_mod(s, 4);
        x += (2 * (k % 2) as i64 - 1) as f64 * s as f64 / m as f64;
        x -= x.floor();
    }
    x
}

fn pdc(n: i64) -> String {
    assert!(n > 50, "Error, n should be bigger than 50");
    let x = digits_of_pi(n);
    let mut pow = 1e9;
    let mut y = x * pow;

    while pow > 10.0 && (y - y.floor() < 0.05 || y - y.floor() > 0.95) {
        pow /= 10.0;
        y = x * pow;
    }

    y.floor().to_string()
}

fn trace_join(prev: &str, new: &str) -> String {
    for s in (0..new.len()).rev() {
        if let Some(pos) = prev.rfind(&new[..=s]) {
            if pos >= prev.len().saturating_sub(10) {
                return format!("{}{}", &prev[..pos], new);
            }
        }
    }
    new.to_string()
}

fn main() -> Result<(), Box<dyn Error>> {
    let pause_min_time = Duration::from_secs_f64(0.05);
    let n = 51;
    let prefix = "π = 3.141592653589793238462643383279502884197169399375105";

    for c in prefix.chars() {
        print!("{}", c);
        std::io::Write::flush(&mut std::io::stdout())?;
        sleep(pause_min_time);
    }

    let mut trace = pdc(n);
    let mut n = n;

    loop {
        let timestamp = Instant::now();
        trace = trace_join(&trace, &pdc(n));
        let delta = timestamp.elapsed();

        if delta < pause_min_time {
            sleep(pause_min_time - delta);
        }

        print!(
            "{}",
            trace.chars().nth((n - 51) as usize).unwrap_or_default()
        );
        std::io::Write::flush(&mut std::io::stdout())?;
        n += 1;
    }
}
