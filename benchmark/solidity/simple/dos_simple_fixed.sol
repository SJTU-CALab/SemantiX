pragma solidity ^0.4.24;

contract DosOneFunc {

    address[] listAddresses;

    function ifillArray() public returns (bool){
        listAddresses.push(msg.sender);
            return true;
    }
}
