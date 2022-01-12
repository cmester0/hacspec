src/MachineIntegers.vo src/MachineIntegers.glob src/MachineIntegers.v.beautified src/MachineIntegers.required_vo: src/MachineIntegers.v 
src/MachineIntegers.vio: src/MachineIntegers.v 
src/MachineIntegers.vos src/MachineIntegers.vok src/MachineIntegers.required_vos: src/MachineIntegers.v 
src/Lib.vo src/Lib.glob src/Lib.v.beautified src/Lib.required_vo: src/Lib.v src/MachineIntegers.vo
src/Lib.vio: src/Lib.v src/MachineIntegers.vio
src/Lib.vos src/Lib.vok src/Lib.required_vos: src/Lib.v src/MachineIntegers.vos
src/QuickChickLib.vo src/QuickChickLib.glob src/QuickChickLib.v.beautified src/QuickChickLib.required_vo: src/QuickChickLib.v src/Lib.vo src/MachineIntegers.vo src/Lib.vo
src/QuickChickLib.vio: src/QuickChickLib.v src/Lib.vio src/MachineIntegers.vio src/Lib.vio
src/QuickChickLib.vos src/QuickChickLib.vok src/QuickChickLib.required_vos: src/QuickChickLib.v src/Lib.vos src/MachineIntegers.vos src/Lib.vos
src/Bls12_381.vo src/Bls12_381.glob src/Bls12_381.v.beautified src/Bls12_381.required_vo: src/Bls12_381.v src/Lib.vo src/MachineIntegers.vo src/QuickChickLib.vo src/Lib.vo
src/Bls12_381.vio: src/Bls12_381.v src/Lib.vio src/MachineIntegers.vio src/QuickChickLib.vio src/Lib.vio
src/Bls12_381.vos src/Bls12_381.vok src/Bls12_381.required_vos: src/Bls12_381.v src/Lib.vos src/MachineIntegers.vos src/QuickChickLib.vos src/Lib.vos
src/Chacha20.vo src/Chacha20.glob src/Chacha20.v.beautified src/Chacha20.required_vo: src/Chacha20.v src/Lib.vo src/MachineIntegers.vo src/Lib.vo
src/Chacha20.vio: src/Chacha20.v src/Lib.vio src/MachineIntegers.vio src/Lib.vio
src/Chacha20.vos src/Chacha20.vok src/Chacha20.required_vos: src/Chacha20.v src/Lib.vos src/MachineIntegers.vos src/Lib.vos
src/Poly1305.vo src/Poly1305.glob src/Poly1305.v.beautified src/Poly1305.required_vo: src/Poly1305.v src/Lib.vo src/MachineIntegers.vo src/Lib.vo
src/Poly1305.vio: src/Poly1305.v src/Lib.vio src/MachineIntegers.vio src/Lib.vio
src/Poly1305.vos src/Poly1305.vok src/Poly1305.required_vos: src/Poly1305.v src/Lib.vos src/MachineIntegers.vos src/Lib.vos
src/Chacha20poly1305.vo src/Chacha20poly1305.glob src/Chacha20poly1305.v.beautified src/Chacha20poly1305.required_vo: src/Chacha20poly1305.v src/Lib.vo src/MachineIntegers.vo src/Lib.vo src/Chacha20.vo src/Poly1305.vo
src/Chacha20poly1305.vio: src/Chacha20poly1305.v src/Lib.vio src/MachineIntegers.vio src/Lib.vio src/Chacha20.vio src/Poly1305.vio
src/Chacha20poly1305.vos src/Chacha20poly1305.vok src/Chacha20poly1305.required_vos: src/Chacha20poly1305.v src/Lib.vos src/MachineIntegers.vos src/Lib.vos src/Chacha20.vos src/Poly1305.vos
src/Curve25519.vo src/Curve25519.glob src/Curve25519.v.beautified src/Curve25519.required_vo: src/Curve25519.v src/Lib.vo src/MachineIntegers.vo src/Lib.vo
src/Curve25519.vio: src/Curve25519.v src/Lib.vio src/MachineIntegers.vio src/Lib.vio
src/Curve25519.vos src/Curve25519.vok src/Curve25519.required_vos: src/Curve25519.v src/Lib.vos src/MachineIntegers.vos src/Lib.vos
src/Sha256.vo src/Sha256.glob src/Sha256.v.beautified src/Sha256.required_vo: src/Sha256.v src/Lib.vo src/MachineIntegers.vo src/Lib.vo
src/Sha256.vio: src/Sha256.v src/Lib.vio src/MachineIntegers.vio src/Lib.vio
src/Sha256.vos src/Sha256.vok src/Sha256.required_vos: src/Sha256.v src/Lib.vos src/MachineIntegers.vos src/Lib.vos
src/Aes.vo src/Aes.glob src/Aes.v.beautified src/Aes.required_vo: src/Aes.v src/Lib.vo src/MachineIntegers.vo src/Lib.vo
src/Aes.vio: src/Aes.v src/Lib.vio src/MachineIntegers.vio src/Lib.vio
src/Aes.vos src/Aes.vok src/Aes.required_vos: src/Aes.v src/Lib.vos src/MachineIntegers.vos src/Lib.vos
src/Concordium_Impls.vo src/Concordium_Impls.glob src/Concordium_Impls.v.beautified src/Concordium_Impls.required_vo: src/Concordium_Impls.v src/Lib.vo src/MachineIntegers.vo src/Lib.vo
src/Concordium_Impls.vio: src/Concordium_Impls.v src/Lib.vio src/MachineIntegers.vio src/Lib.vio
src/Concordium_Impls.vos src/Concordium_Impls.vok src/Concordium_Impls.required_vos: src/Concordium_Impls.v src/Lib.vos src/MachineIntegers.vos src/Lib.vos
src/Auction.vo src/Auction.glob src/Auction.v.beautified src/Auction.required_vo: src/Auction.v src/Lib.vo src/MachineIntegers.vo src/QuickChickLib.vo src/Lib.vo
src/Auction.vio: src/Auction.v src/Lib.vio src/MachineIntegers.vio src/QuickChickLib.vio src/Lib.vio
src/Auction.vos src/Auction.vok src/Auction.required_vos: src/Auction.v src/Lib.vos src/MachineIntegers.vos src/QuickChickLib.vos src/Lib.vos
