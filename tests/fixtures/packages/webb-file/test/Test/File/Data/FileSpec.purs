module Test.File.Data.FileSpec where

import Test.Prelude

import Data.Maybe (isNothing)
import Data.String as String
import Node.FS (FileDescriptor)
import Unsafe.Coerce (unsafeCoerce)
import Webb.Directory.Data.Absolute as Abs
import Webb.File.Data.File as File
import Webb.Stateful (localEffect)

spec :: Spec Unit
spec = describe "File data model tests" do
  it "empty" do
    String.length (File.id file) > 15 === true
    Abs.basename (File.path file) === "file"
    File.position file === 0
    File.isAppending file === false
    File.isOpen file === false
    isNothing (File.fd file) === true
    
  it "setting and updating position" do
    let f = File.updatePosition (_ - 1) file
    posEquals f (-1)
    let f' = File.setPosition 200 file
    posEquals f' 200
    
  it "loading and unloading a file descriptor" do
    let fd = unsafeCoerce unit :: FileDescriptor 

    let f = File.loadFd fd file
    isOpen f

    let f' = File.unloadFd file
    isClosed f'
    
  where 
  file = localEffect do
    File.emptyFile $ Abs.new ["/"] "file"
    
  posEquals f n = do
    File.position f === n
    
  isOpen f = do
    File.isOpen f === true

  isClosed f = do
    File.isOpen f === false
    
