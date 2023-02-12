{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_MixedDecisionDiagrams (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude


#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath



bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/home/dushiel/MDD/MixedDecisionDiagrams/.stack-work/install/x86_64-linux-tinfo6/20d87b77f6a198dd6ce7e69196ad6c6eb3cd416325e244f44755b720d1fb8c2d/9.4.4/bin"
libdir     = "/home/dushiel/MDD/MixedDecisionDiagrams/.stack-work/install/x86_64-linux-tinfo6/20d87b77f6a198dd6ce7e69196ad6c6eb3cd416325e244f44755b720d1fb8c2d/9.4.4/lib/x86_64-linux-ghc-9.4.4/MixedDecisionDiagrams-0.1.0.0-WfqKnhPWbJJPmveldKITD-MixedDecisionDiagrams"
dynlibdir  = "/home/dushiel/MDD/MixedDecisionDiagrams/.stack-work/install/x86_64-linux-tinfo6/20d87b77f6a198dd6ce7e69196ad6c6eb3cd416325e244f44755b720d1fb8c2d/9.4.4/lib/x86_64-linux-ghc-9.4.4"
datadir    = "/home/dushiel/MDD/MixedDecisionDiagrams/.stack-work/install/x86_64-linux-tinfo6/20d87b77f6a198dd6ce7e69196ad6c6eb3cd416325e244f44755b720d1fb8c2d/9.4.4/share/x86_64-linux-ghc-9.4.4/MixedDecisionDiagrams-0.1.0.0"
libexecdir = "/home/dushiel/MDD/MixedDecisionDiagrams/.stack-work/install/x86_64-linux-tinfo6/20d87b77f6a198dd6ce7e69196ad6c6eb3cd416325e244f44755b720d1fb8c2d/9.4.4/libexec/x86_64-linux-ghc-9.4.4/MixedDecisionDiagrams-0.1.0.0"
sysconfdir = "/home/dushiel/MDD/MixedDecisionDiagrams/.stack-work/install/x86_64-linux-tinfo6/20d87b77f6a198dd6ce7e69196ad6c6eb3cd416325e244f44755b720d1fb8c2d/9.4.4/etc"

getBinDir     = catchIO (getEnv "MixedDecisionDiagrams_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "MixedDecisionDiagrams_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "MixedDecisionDiagrams_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "MixedDecisionDiagrams_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "MixedDecisionDiagrams_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "MixedDecisionDiagrams_sysconfdir") (\_ -> return sysconfdir)




joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/'
