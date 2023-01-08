use std::fmt;

use crate::point::{AsPointSlice, Point};

use super::Perm;

pub fn display_perm<Pt: Point>(
    perm: &Perm<[Pt]>,
    f: &mut impl fmt::Write,
    offset: usize,
    sep: char,
) -> fmt::Result {
    let mut seen = vec![false; perm.degree()];

    let mut written = false;

    for a in perm.domain() {
        let mut b = perm.image(a);
        if a == b || seen[a.index()] {
            continue;
        }
        seen[a.index()] = true;

        written = true;
        write!(
            f,
            "({a}{sep}{b}",
            a = a.index() + offset,
            b = b.index() + offset,
        )?;

        loop {
            seen[b.index()] = true;
            b = perm.image(b);
            if b == a {
                break;
            }

            write!(f, "{sep}{b}", b = b.index() + offset,)?;
        }
        write!(f, ")")?;
    }

    if !written {
        write!(f, "()")?;
    }

    Ok(())
}

pub fn debug_perm<Pt: Point>(
    perm: &Perm<[Pt]>,
    f: &mut fmt::Formatter,
    offset: usize,
    sep: char,
) -> fmt::Result {
    if perm.degree() == 0 {
        write!(f, "()")?;
    } else {
        display_perm(perm, f, offset, sep)?;
        let last_pt = Pt::from_index(perm.degree() - 1);
        if perm.image(last_pt) == last_pt {
            write!(f, "({})", last_pt.index() + offset)?;
        }
    }

    Ok(())
}

impl<T: AsPointSlice + ?Sized> fmt::Display for Perm<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_perm(self.as_ref(), f, 0, ' ')
    }
}

impl<T: AsPointSlice + ?Sized> fmt::Debug for Perm<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        debug_perm(self.as_ref(), f, 0, ' ')
    }
}
