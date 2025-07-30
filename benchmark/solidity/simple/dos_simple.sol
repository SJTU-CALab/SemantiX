pragma solidity ^0.4.24;

contract DosOneFunc {

    address[] listAddresses;

    function ifillArray() public returns (bool){
        for(uint i=0;i<350;i++) {
                listAddresses.push(msg.sender);
        }
            return true;
    }
}
