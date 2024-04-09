use std::{
    collections::HashMap,
    env,
    fs::File,
    hash::Hash,
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

fn convert_jump(s: Option<&str>) -> u16 {
    match s {
        None => 0b000,
        Some("JGT") => 0b001,
        Some("JEQ") => 0b010,
        Some("JGE") => 0b011,
        Some("JLT") => 0b100,
        Some("JNE") => 0b101,
        Some("JLE") => 0b110,
        Some("JMP") => 0b111,
        Some(_) => panic!("Invalid jump"),
    }
}

fn convert_dest(s: Option<&str>) -> u16 {
    match s {
        None => 0b000,
        Some("M") => 0b001,
        Some("D") => 0b010,
        Some("DM") => 0b011,
        Some("A") => 0b100,
        Some("AM") => 0b101,
        Some("AD") => 0b110,
        Some("ADM") => 0b111,
        Some(_) => panic!("Invalid dest"),
    }
}

fn convert_comp(s: &str) -> u16 {
    match s {
        "0" => 0b0_101_010,
        "1" => 0b0_111_111,
        "-1" => 0b0_111_010,
        "D" => 0b0_001_100,
        "A" => 0b0_110_000,
        "M" => 0b1_110_000,
        "!D" => 0b0_001_101,
        "!A" => 0b0_110_001,
        "!M" => 0b1_110_001,
        "-D" => 0b0_001_111,
        "-A" => 0b0_110_011,
        "-M" => 0b1_110_011,
        "D+1" => 0b0_011_111,
        "A+1" => 0b0_110_111,
        "M+1" => 0b1_110_111,
        "D-1" => 0b0_001_110,
        "A-1" => 0b0_110_010,
        "M-1" => 0b1_110_010,
        "D+A" => 0b0_000_010,
        "D+M" => 0b1_000_010,
        "D-A" => 0b0_010_011,
        "D-M" => 0b1_010_011,
        "A-D" => 0b0_000_111,
        "M-D" => 0b1_000_111,
        "D&A" => 0b0_000_000,
        "D&M" => 0b1_000_000,
        "D|A" => 0b0_010_101,
        "D|M" => 0b1_010_101,
        _ => panic!("Invalid comp"),
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Comp<'a> {
    dest: Option<&'a str>,
    comp: &'a str,
    jump: Option<&'a str>,
}
impl<'a> Comp<'a> {
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
    fn as_code(&self) -> u16 {
        todo!()
    }
}

#[derive(Debug, PartialEq, Eq)]
enum ParsedInstruction<'a> {
    Label(&'a str),
    Address(&'a str),
    Computation(Comp<'a>),
}

impl<'a> ParsedInstruction<'a> {
    fn parse_instruction(s: &str) -> ParsedInstruction<'_> {
        if &s[..1] == "(" {
            ParsedInstruction::Label(&s[1..s.len() - 1])
        } else if &s[..1] == "@" {
            ParsedInstruction::Address(&s[1..])
        } else {
            ParsedInstruction::Computation(Comp::parse_comp(s))
        }
    }

    fn snd_pass(&self, symbol_table: &SymbolTable) -> String {
        match self {
            ParsedInstruction::Label(l) => {
                let code = *symbol_table.labels.get(*l).unwrap();
                // let code = code | 0b1_000000000000000;
                format!("{:016b}", code)
            }
            ParsedInstruction::Address(a) => {
                if a.chars().all(|c| c.is_ascii_digit()) {
                    let code = a.parse::<u16>().unwrap();
                    format!("{:016b}", code)
                } else {
                    let code = *symbol_table.labels.get(*a).unwrap();
                    // let code = code | 0b1_000000000000000;
                    format!("{:016b}", code)
                }
            }
            ParsedInstruction::Computation(_) => todo!(),
        }
    }
}

struct SymbolTable {
    labels: HashMap<String, u16>,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self {
            labels: HashMap::from_iter([
                ("R0".into(), 0),
                ("R1".into(), 1),
                ("R2".into(), 2),
                ("R3".into(), 3),
                ("R4".into(), 4),
                ("R5".into(), 5),
                ("R6".into(), 6),
                ("R7".into(), 7),
                ("R8".into(), 8),
                ("R9".into(), 9),
                ("R10".into(), 10),
                ("R11".into(), 11),
                ("R12".into(), 12),
                ("R13".into(), 13),
                ("R14".into(), 14),
                ("R15".into(), 15),
                ("SCP".into(), 0),
                ("LCL".into(), 1),
                ("ARG".into(), 2),
                ("THIS".into(), 3),
                ("THAT".into(), 4),
                ("SCREEN".into(), 16384),
                ("KBD".into(), 24576),
            ]),
        }
    }
}

impl SymbolTable {
    fn fst_pass(pis: &[ParsedInstruction<'_>]) -> Self {
        let mut labels: HashMap<String, u16> = HashMap::new();
        let mut adds: Vec<String> = Vec::new();
        let mut counter = 0;
        for pi in pis.iter() {
            match pi {
                ParsedInstruction::Label(s) => {
                    // Add next line
                    labels.insert(s.to_string(), counter);
                }
                ParsedInstruction::Address(s) => {
                    counter += 1;

                    // Skip numeric addresses
                    if s.chars().all(|c| c.is_ascii_digit()) {
                        continue;
                    }

                    if !labels.contains_key(*s) {
                        adds.push(s.to_string());
                    }
                }
                ParsedInstruction::Computation(_) => {
                    counter += 1;
                }
            }
        }
        let mut add_idx = 16;
        for s in adds.into_iter() {
            labels.entry(s).or_insert_with(|| {
                let tmp = add_idx;
                add_idx += 1;
                tmp
            });
        }
        let mut symtable = SymbolTable::default();
        symtable.labels.extend(labels);
        symtable
    }
}

fn main() -> eyre::Result<()> {
    let mut args = env::args();
    if let Some(path) = args.nth(1) {
        let file = BufReader::new(File::open(path)?);
        let lines: Result<Vec<_>, _> = file.lines().collect();
        let lines = lines?;

        let parsed = lines
            .iter()
            .map(|s| ParsedInstruction::parse_instruction(s))
            .collect::<Vec<_>>();
        let symbol_table = SymbolTable::fst_pass(&parsed);
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_symbol_table() {
        let s = ["(LOOP)", "@sum", "D=M", "@R0", "M=D"]
            .iter()
            .map(|s| ParsedInstruction::parse_instruction(s))
            .collect::<Vec<_>>();
        let st = SymbolTable::fst_pass(&s);
        assert!(st.labels.contains_key("LOOP"));
        assert_eq!(st.labels.get("LOOP").unwrap(), &0);
        assert!(st.labels.contains_key("sum"));
        assert_eq!(st.labels.get("sum").unwrap(), &16);
        assert_eq!(st.labels.len(), 25);
    }

    #[test]
    fn test_instruction() {
        let s = "(LOOP)";
        let pi = ParsedInstruction::parse_instruction(s);
        assert_eq!(pi, ParsedInstruction::Label("LOOP"));

        let s = "@sum";
        let pi = ParsedInstruction::parse_instruction(s);
        assert_eq!(pi, ParsedInstruction::Address("sum"));

        let s = "D=M";
        let pi = ParsedInstruction::parse_instruction(s);
        assert_eq!(
            pi,
            ParsedInstruction::Computation(Comp {
                dest: Some("D"),
                comp: "M",
                jump: None
            })
        );
    }

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
            Comp::parse_comp("D"),
            Comp {
                dest: None,
                comp: "D",
                jump: None,
            }
        );
        assert_eq!(
            Comp::parse_comp("D=M"),
            Comp {
                dest: Some("D"),
                comp: "M",
                jump: None,
            }
        );
        assert_eq!(
            Comp::parse_comp("D=M;JLE"),
            Comp {
                dest: Some("D"),
                comp: "M",
                jump: Some("JLE"),
            }
        );
        assert_eq!(
            Comp::parse_comp("M;JLE"),
            Comp {
                dest: None,
                comp: "M",
                jump: Some("JLE"),
            }
        );
        assert_eq!(
            Comp::parse_comp("MD=D+1"),
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
