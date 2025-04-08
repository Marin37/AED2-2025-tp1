```java
TAD Transaccion {
    obs id_transaccion: natural
    obs id_comprador: int
    obs id_vendedor: natural
    obs monto: natural
}

TAD Bloque {
    obs transacciones: seq<Transaccion>
    obs n_bloque: natural
}

TAD BlockChain {
    obs bloques: seq<Bloque>
}

// FALTAN OPERACIONES DE INICIACION DE TADS

TAD $BerretaCoin {
    obs blockchain: BlockChain

    aux ultimoBloque (in blockchain: BlockChain): Bloque {
        res.n_bloque = |blockchain.bloques| - 1
    }

    aux primeraTransaccion (in bloque: Bloque): Transaccion {
        (|bloque.transacciones| > 0) -> bloque.transacciones[0]
    }
    
    pred esTransacciondeCreacion(in transaccion: Transaccion) {
        True <-> ((transaccion.id_comprador = 0) ^ (transaccion.monto = 1))
    }
    pred esBloqueConTransacciondeCreacion(in bloque: Bloque) {
        True <-> esTransacciondeCreacion(bloque.transacciones[0])
    }

    aux coinsEnBloque(in: id_usuario: int, in: bloque: Bloque): int {
        Sum_{i=0}^{|bloque.transacciones| - 1} (
            IfThenElseFi(
                bloque.transacciones[i].id_comprador == id_usuario, 
                - bloque.transacciones[i].monto, 
                IfThenElseFi(
                    bloque.transacciones[i].id_vendedor == id_usuario, 
                    bloque.transacciones[i].monto, 
                    0)
            )
        )
    }

    aux coinsEnCuenta(in: id_usuario: int, in: blockchain: Blockchain): int {
        Sum_{i=0}^{|blockchain.bloques| - 1}(
            coinsEnBloque(id_usuario, blockhain.bloques[i])
        )
    }

    // COMPLETAR aux esBlockChainValida

    aux esTransaccionValida(in transaccion: Transaccion, in blockchain: BlockChain): bool {
        (paraCada i:Z) ( 
                transaccion[i].monto <= coinsEnCuenta(transaccion[i].id_comprador, blockchain) ^
                (transaccion[i].id_comprador != transaccion[i].id_vendedor) ^
                (esTransaccionUnica(transaccion, BlockChain))
            )
    } // Preguntar si se puede aux en aux, pred en pred, o cualquiera (y si se vale cambiar un pred por un aux q devuelva bool)


    proc agregarBloque (in transacciones: seq<Transaccion>, inout blockchain: BlockChain) {
        requiere {(|transacciones| > 0) ^ (|transacciones| <= 50) ^ (paraTodo i:Z)
             (0 < i < |transacciones|) -> 
                (esTransaccionValida(transacciones[i]))}
        requiere {blockchain = BC_0}
        asegura {|blockchain.bloques| = |BC_0.bloques| + 1}
        asegura {(ultimoBloque(BC_0).n_bloque < 3000) -> 
                esTransacciondeCreacion(transacciones[0])}
        // esBloqueConTransacciondeCreacion(ultimoBloque(blockchain))}
    }


    // maximosTenedores: devuelve una lista que contiene al o los usuarios que tienen la mayor cantidad de $Berretacoin

    aux usuariosUnicosEnBloque(in bloque: Bloque): seq<N> {
        (paraTodo i:Z) (0 < i < |bloque| -> IfThenElseFi(bloque.transacciones[i].id_comprador not in res, concat(res, <bloque.transacciones[i].id_comprador>), 
            IfThenElseFi(bloque.transacciones[i].id_vendedor not in res, concat(res(bloque, <bloque.transacciones[i].id_vendedor>), concat(res, < >)))))
    } // VER SI ESTA BIEN

    aux usuariosUnicos(in blockchain: BlockChain): seq<N> {
        // devuelve lista de usuarios
        (paraTodo i:Z) ()

    }

    proc maximosTenedores (in blockchain: BlockChain): seq<N> {
        requiere {|blockchain.bloques| > 0}
        requiere {esBlockChainValida(BlockChain)}
        asegura {(paraTodo i:Z) 
                    (0 < i < |usuariosUnicos(blockchain)|) -> 
                        coinsEnCuenta(res[0]) <= coinsEnCuenta(usuariosUnicos[i]) } //no hace falta verificar el resto de res xq tienen todos igual plata
    }

    aux transaccionUnica (id_transaccion: natural, blockchain: BlockChain) : bool {
        (paratodo i : Z) ((paratodo j : Z) (0 <= i <= |blockhain.bloques|) ^ (0 <= j <= |blockhain.bloques[i]|) -> id_transaccion != blockhain.bloques[i].transacciones[j].id_transaccion)
    }


        
            // proc agregarTransaccion (in id_comprador: int, in id_vendedor: natural, in monto: natural, inout blockchain: BlockChain) {
            //     requiere {id_comprador != id_vendedor}
            //     asegura {transaccionUnica(res[0], blockchain)}
            // }
}
```
