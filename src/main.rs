use std::{
    env,
    fs::File,
    io::{BufRead, BufReader},
};

fn remove_whitespace_comments(mut s: &str) -> Option<String> {
    if let Some(comment_idx) = s.find("//") {
        s = &s[..comment_idx];
    }

    let res: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    if res.is_empty() {
        None
    } else {
        Some(res)
    }
}

fn convert_comp(s: &str) -> u16 {
    match s {
        "0" => 0b101_010,
        "1" => 0b111_111,
        "-1" => 0b111_010,
        "D" => 0b001_100,
        "D+1" => 0b011_111,
        _ => panic!("Invalid operation"),
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Comp<'a> {
    dest: Option<&'a str>,
    comp: &'a str,
    jump: Option<&'a str>,
}

fn parse_comp(mut s: &str) -> Comp {
    let dest = {
        if let Some(idx) = s.find('=') {
            let d = &s[..idx];
            s = &s[idx + 1..];
            Some(d)
        } else {
            None
        }
    };
    let jump = {
        if let Some(idx) = s.find(';') {
            let j = &s[idx + 1..];
            s = &s[..idx];
            Some(j)
        } else {
            None
        }
    };
    Comp {
        dest,
        comp: s,
        jump,
    }
}

enum Instruction<'a> {
    Label(u16),
    Address(u16),
    Computation(Comp<'a>),
}

fn main() -> eyre::Result<()> {
    let mut args = env::args();
    if let Some(path) = args.nth(1) {
        let file = BufReader::new(File::open(path)?);
        let lines: Result<Vec<_>, _> = file.lines().collect();
        let lines = lines?;
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_remove_whitespace() {
        assert_eq!(remove_whitespace_comments("D = M"), Some("D=M".into()));
        assert_eq!(
            remove_whitespace_comments("D = M    // test"),
            Some("D=M".into())
        );
        assert_eq!(remove_whitespace_comments("// COmment"), None);
        assert_eq!(
            remove_whitespace_comments("M = 1; JMP"),
            Some("M=1;JMP".into())
        );
    }

    #[test]
    fn test_parse_comp() {
        assert_eq!(
            parse_comp("D"),
            Comp {
                dest: None,
                comp: "D",
                jump: None,
            }
        );
        assert_eq!(
            parse_comp("D=M"),
            Comp {
                dest: Some("D"),
                comp: "M",
                jump: None,
            }
        );
        assert_eq!(
            parse_comp("D=M;JLE"),
            Comp {
                dest: Some("D"),
                comp: "M",
                jump: Some("JLE"),
            }
        );
        assert_eq!(
            parse_comp("M;JLE"),
            Comp {
                dest: None,
                comp: "M",
                jump: Some("JLE"),
            }
        );
        assert_eq!(
            parse_comp("MD=D+1"),
            Comp {
                dest: Some("MD"),
                comp: "D+1",
                jump: None,
            }
        );
    }

    #[test]
    fn test_output_binary_rep() {
        assert_eq!("010", format!("{:03b}", 0b010));
    }
}
