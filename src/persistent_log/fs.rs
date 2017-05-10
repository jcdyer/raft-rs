use std::{error, fmt, fs, path, result};
use std::io::prelude::*;
use std::io::SeekFrom;

use persistent_log::Log;
use LogIndex;
use ServerId;
use Term;

/// This is a `Log` implementation that stores entries in the filesystem
/// as well as in a struct. It is chiefly intended for testing.
///
/// # Panic
///
/// No bounds checking is performed and attempted access to non-existing log
/// indexes will panic.


/// Error type for FsLog

#[derive(Debug, PartialEq, Eq)]
pub struct Error;

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "An error occurred")
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        "An error occurred"
    }
}

impl ::std::convert::From<::std::io::Error> for Error {
    fn from(err: ::std::io::Error) -> Error {
        Error
    }
}


#[derive(Debug)]
pub struct FsLog {
    file: fs::File,
    current_term: Term,
    voted_for: Option<ServerId>,
    entries: Vec<(Term, Vec<u8>)>,
}

impl Clone for FsLog {
    fn clone(&self) -> FsLog {
        // Wish I didn't have to unwrap the filehandle...
        FsLog {
            file: self.file.try_clone().unwrap(),
            current_term: self.current_term.clone(),
            voted_for: self.voted_for.clone(),
            entries: self.entries.clone(),
        }
    }
}
    
fn u64_from_u8s(input: &[u8]) -> Option<u64> {
    if input.len() != 8 {
        None 
    } else {
        Some(
            ((input[0] as u64) << 56)
            + ((input[1] as u64) << 48)
            + ((input[2] as u64) << 40)
            + ((input[3] as u64) << 32)
            + ((input[4] as u64) << 24)
            + ((input[5] as u64) << 16)
            + ((input[6] as u64) << 8)
            + (input[7] as u64)
        )
    }
}

fn u64_to_u8s(input: u64) -> [u8; 8] {
    [
        (input >> 56) as u8, 
        ((input >> 48) & 0xff) as u8,
        ((input >> 40) & 0xff) as u8,
        ((input >> 32) & 0xff) as u8,
        ((input >> 24) & 0xff) as u8,
        ((input >> 16) & 0xff) as u8,
        ((input >> 8) & 0xff) as u8,
        (input & 0xff) as u8,
    ]
}

/// Stores log as 8 bytes for current_term, 8 bytes for voted_for, and 
/// As much as needed for the log.
impl FsLog {
    pub fn new(filename: &path::Path) -> Result<FsLog, Error> {
        let mut f = fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(filename)?;

        let mut buf = [0u8; 8];
        let voted_buf = [0xff as u8; 8];
        
        { 
            let mut read_buf = Vec::new();
            f.read_to_end(&mut read_buf).unwrap();
            println!("Read: {:?}", read_buf);
            f.seek(SeekFrom::Start(0)).unwrap();
        }
                 
        assert_eq!(f.seek(SeekFrom::Start(0)).unwrap(), 0);
        if f.metadata()?.len() == 0 {
            println!("Empty file");
            f.write_all(&buf)?;
            f.write_all(&voted_buf)?;
            f.seek(SeekFrom::Start(0))?;
        }

        f.read_exact(&mut buf)?;
        let current_term: Term = u64_from_u8s(&buf).unwrap().into();

        f.read_exact(&mut buf)?;
        let voted_for: Option<ServerId> = match u64_from_u8s(&buf).unwrap() {
            x if x == <u64>::max_value() => None,
            x => Some(x.into())
        };

        let log = FsLog {
            file: f,
            current_term: current_term,
            voted_for: voted_for,
            entries: Vec::new(),
        };
        Ok(log)
    }

    fn print_file(&mut self) -> Result<(), Error> {
        let mut buf = Vec::new();
        self.file.seek(SeekFrom::Start(0))?;
        self.file.read_to_end(&mut buf)?;
        println!("File: {:?}", buf);
        Ok(())
    }

    fn write_term(&mut self) -> Result<(), Error> {
        self.file.seek(SeekFrom::Start(0))?;
        self.file.write_all(&u64_to_u8s(self.current_term.into())[..])?;
        self.write_voted_for()?;
        Ok(())
    }
    
    fn write_voted_for(&mut self) -> Result<(), Error> {
        self.file.seek(SeekFrom::Start(8))?;
        self.file.write_all(
            &match self.voted_for {
                None => u64_to_u8s(<u64>::max_value()),
                Some(ServerId(n)) => u64_to_u8s(n),
            }[..]
        )?;
        Ok(())
    }
}

impl Log for FsLog {
    type Error = Error;

    fn current_term(&self) -> result::Result<Term, Error> {
        Ok(self.current_term)
    }

    fn set_current_term(&mut self, term: Term) -> result::Result<(), Error> {
        self.current_term = term;
        self.voted_for = None;
        self.write_term()?;
        Ok(())
    }

    fn inc_current_term(&mut self) -> result::Result<Term, Error> {
        self.current_term = self.current_term + 1;
        self.voted_for = None;
        self.write_term()?;
        self.current_term()
    }

    fn voted_for(&self) -> result::Result<Option<ServerId>, Error> {
        Ok(self.voted_for)
    }

    fn set_voted_for(&mut self, address: ServerId) -> result::Result<(), Error> {
        self.voted_for = Some(address);
        self.write_voted_for()?;
        Ok(())
    }

    fn latest_log_index(&self) -> result::Result<LogIndex, Error> {
        Ok(LogIndex(self.entries.len() as u64))
    }

    fn latest_log_term(&self) -> result::Result<Term, Error> {
        let len = self.entries.len();
        if len == 0 {
            Ok(Term::from(0))
        } else {
            Ok(self.entries[len - 1].0)
        }
    }

    fn entry(&self, index: LogIndex) -> result::Result<(Term, &[u8]), Error> {
        let (term, ref bytes) = self.entries[(index - 1).as_u64() as usize];
        Ok((term, bytes))
    }

    /// Append entries sent from the leader.  
    /// FIXME: This is contrary to the raft spec, and will cause errors, as it discards entries that may be
    /// necessary.  The entries should not be truncated unless a mismatch is found.
    fn append_entries(&mut self,
                      from: LogIndex,
                      entries: &[(Term, &[u8])])
                      -> result::Result<(), Error> {
        assert!(self.latest_log_index().unwrap() + 1 >= from);
        self.entries.truncate((from - 1).as_u64() as usize);  
        Ok(self.entries.extend(entries.iter().map(|&(term, command)| (term, command.to_vec()))))
    }
}

#[cfg(test)]
mod test {
    use std::fs::remove_file;
    use std::path::Path;
    use super::*;
    use LogIndex;
    use ServerId;
    use Term;
    use persistent_log::Log;

    #[test]
    fn test_current_term() {
        let filename = Path::new("/tmp/raft-store.1");
        remove_file(&filename).unwrap_or(());
        let mut store = FsLog::new(&filename).unwrap();
        assert_eq!(Term(0), store.current_term().unwrap());
        store.set_voted_for(ServerId::from(0)).unwrap();
        store.set_current_term(Term(42)).unwrap();
        assert_eq!(None, store.voted_for().unwrap());
        assert_eq!(Term(42), store.current_term().unwrap());
        store.inc_current_term().unwrap();
        assert_eq!(Term(43), store.current_term().unwrap());
        remove_file(&filename).unwrap();
    }

    #[test]
    fn test_voted_for() {
        let filename = Path::new("/tmp/raft-store.2");
        remove_file(&filename).unwrap_or(());
        let mut store = FsLog::new(&filename).unwrap();
        assert_eq!(None, store.voted_for().unwrap());
        let id = ServerId::from(0);
        store.set_voted_for(id).unwrap();
        assert_eq!(Some(id), store.voted_for().unwrap());
        remove_file(&filename).unwrap();
    }

    #[test]
    fn test_append_entries() {
        let filename = Path::new("/tmp/raft-store.3");
        remove_file(&filename).unwrap_or(());
        let mut store = FsLog::new(&filename).unwrap();
        assert_eq!(LogIndex::from(0), store.latest_log_index().unwrap());
        assert_eq!(Term::from(0), store.latest_log_term().unwrap());

        // [0.1, 0.2, 0.3, 1.4]
        store.append_entries(LogIndex(1),
                             &[(Term::from(0), &[1]),
                               (Term::from(0), &[2]),
                               (Term::from(0), &[3]),
                               (Term::from(1), &[4])])
             .unwrap();
        assert_eq!(LogIndex::from(4), store.latest_log_index().unwrap());
        assert_eq!(Term::from(1), store.latest_log_term().unwrap());
        assert_eq!((Term::from(0), &*vec![1u8]),
                   store.entry(LogIndex::from(1)).unwrap());
        assert_eq!((Term::from(0), &*vec![2u8]),
                   store.entry(LogIndex::from(2)).unwrap());
        assert_eq!((Term::from(0), &*vec![3u8]),
                   store.entry(LogIndex::from(3)).unwrap());
        assert_eq!((Term::from(1), &*vec![4u8]),
                   store.entry(LogIndex::from(4)).unwrap());

        // [0.1, 0.2, 0.3]
        store.append_entries(LogIndex::from(4), &[]).unwrap();
        assert_eq!(LogIndex(3), store.latest_log_index().unwrap());
        assert_eq!(Term::from(0), store.latest_log_term().unwrap());
        assert_eq!((Term::from(0), &*vec![1u8]),
                   store.entry(LogIndex::from(1)).unwrap());
        assert_eq!((Term::from(0), &*vec![2u8]),
                   store.entry(LogIndex::from(2)).unwrap());
        assert_eq!((Term::from(0), &*vec![3u8]),
                   store.entry(LogIndex::from(3)).unwrap());

        // [0.1, 0.2, 2.3, 3.4]
        store.append_entries(LogIndex::from(3), &[(Term(2), &[3]), (Term(3), &[4])]).unwrap();
        assert_eq!(LogIndex(4), store.latest_log_index().unwrap());
        assert_eq!(Term::from(3), store.latest_log_term().unwrap());
        assert_eq!((Term::from(0), &*vec![1u8]),
                   store.entry(LogIndex::from(1)).unwrap());
        assert_eq!((Term::from(0), &*vec![2u8]),
                   store.entry(LogIndex::from(2)).unwrap());
        assert_eq!((Term::from(2), &*vec![3u8]),
                   store.entry(LogIndex::from(3)).unwrap());
        assert_eq!((Term::from(3), &*vec![4u8]),
                   store.entry(LogIndex::from(4)).unwrap());
        remove_file(&filename).unwrap();
    }

    #[test]
    fn test_restore_log() {
        let filename = Path::new("/tmp/raft-store.4");
        remove_file(&filename).unwrap_or(());
        {
            let mut store = FsLog::new(&filename).unwrap();
            store.set_current_term(Term(42)).unwrap();
            store.set_voted_for(ServerId::from(4)).unwrap();
            store.append_entries(LogIndex(1),
                                &[(Term::from(0), &[1]),
                                (Term::from(0), &[2]),
                                (Term::from(0), &[3]),
                                (Term::from(1), &[4])])
                .unwrap();
            println!("Voted for: {:?}", store.voted_for());
            println!("Print file");
            store.print_file();
        }

        // New store with the same backing file starts with the same state.
        let mut store = FsLog::new(&filename).unwrap();
        println!("Print restored file");
        store.print_file();
        assert_eq!(store.voted_for().unwrap(), Some(ServerId::from(4)));
        assert_eq!(store.current_term().unwrap(), Term(42));
        assert_eq!(
            store.entry(LogIndex::from(4)).unwrap(),
            (Term::from(1), &*vec![4u8])
        );
        remove_file(&filename).unwrap();
    }
}
