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

    // procs de creacion
    proc crearTransaccion(in id_transaccion, in id_comprador, in id_vendedor, in monto): Transaccion{
        requiere{id_comprador != id_vendedor}
        asegura{res.id_comprador = id_comprador}
        asegura{res.id_vendedor = id_vendedor}
        asegura{res.id_transaccion = id_transaccion}
        asegura{res.monto = monto}
    }

    proc crearBloque(in transacciones: seq<Transaccion>, in n_bloque: int): Bloque{
        asegura{res.transacciones = transacciones}
        asegura{res.n_bloque = n_bloque}
    }

    proc crearBlockChain(in bloques: seq<Bloques>): BlockChain{
        asegura{res = bloques}
    }

    //Validaciones
    //// TRANSACCION

     // VER SI ESTA BIEN LA VERIFICACION DE ID_TRANSACCION UNICO
    pred esTransaccionUnica (id_transaccion: natural, blockchain: BlockChain){
        (paratodo i : Z) ((paratodo j : Z) (0 <= i <= |blockhain|) ^ (0 <= j <= |blockhain[i]|) -->L id_transaccion != blockhain[i].transacciones[j].id_transaccion)
    }


    pred esTransaccionValida(in transaccion: Transaccion, in blockchain: BlockChain) {
        (paraCada i:Z) ( 
                transaccion[i].monto <= coinsUsuarioEnCuenta(transaccion[i].id_comprador, blockchain) ^
                (transaccion[i].id_comprador != transaccion[i].id_vendedor) ^
                (esTransaccionUnica(transaccion, BlockChain))
            )
    } 

    //// BLOQUE

    // que el n_bloque coincida con el n_bloque que tiene en la blockhain
    pred n_bloqueCorrecto(in bloque: Bloque, in blockchain: BlockChain){
        bloque.n_bloque = blockhain[bloque.n_bloque].n_bloque
    }

    pred longitudBloqueCorrecta(in bloque: Bloque, in blockchain: BlockChain){
         0 <= |bloque.transacciones| <= 50
    }

    pred bloqueDeCreacionCorrecto(in bloque: Bloque, in blockchain: BlockChain){
        (bloque.n_bloque < 3000 -> esTransacciondeCreacion(bloque.transacciones[0])) ^ (bloque.n_bloque >= 3000 -> ¬esTransacciondeCreacion(bloque.transacciones[0]))
    }

    // Verifica que estén ordenadas dentro del bloque (y la distancia sea 1)
    pred transaccionesEnBloqueOrdenadas(in bloque: Bloque, in blockhain: BlockChain){
        (paraTodo i : Z)(0 <= i < |bloque.transacciones| - 1 ->L bloque.transacciones[i].id_transaccion = bloque.transacciones[i+1].id_transaccion - 1 )
    }

    pred esBloqueValido(in bloque: Bloque, in blockchain: BlockChain){
        // no tiene transacciones repetidas (lo quiero verificar de vuelta?)
        // el n_bloque es el que tiene q ser
        // si n_bloque < 3000 -> tiene op de creacion
        (n_bloqueCorrecto(bloque, blockhain)) ^
        (longitudBloqueCorrecta(bloque, blockhain)) ^
        (bloqueDeCreacionCorrecto(bloque, blockhain)) ^
        (transaccionesEnBloqueOrdenadas(bloque, blockhain)) ^
        (paraTodo i:Z)
             (0 <= i <= |bloque.transacciones| - 1) -->L
                (esTransaccionValida(bloques.transacciones[i]))
    }

    //// BLOCKHAIN

    // Verifica que el ultimo de un bloque sea el primero del siguiente - 1
    pred BlockChainOrdenada(in blockhain: BlockChain){
        (paraTodo i:Z) (0 <= i < |blockhain| - 1) ->L blockhain[i].transacciones[ |blockhain[i].transacciones| - 1].id_transaccion = blockhain[i+1].transacciones[0].id_transaccion - 1
    }


    pred esBlockChainValida(in blockhain: BlockChain){
        // todos los bloques son validos
        // para cada bloque, todos los id_transaccion son > al de todos los anteriores

        (BlockChainOrdenada(blockhain)) ^
        (paraTodo i:Z) (0 <= i <= |blockhain| - 1 ->L esBloqueValido(bloque, blockhain))
    }
    ////

    // aux ultimoBloque (in blockchain: BlockChain): Bloque {
    //     res.n_bloque = |blockchain| - 1
    // }

    
    pred esTransacciondeCreacion(in transaccion: Transaccion) {
        ((transaccion.id_comprador = 0) ^ (transaccion.monto = 1))
    }


    aux coinsUsuarioEnBloque(in: id_usuario: int, in: bloque: Bloque): int {
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

    aux coinsUsuarioEnCuenta(in: id_usuario: int, in: blockchain: Blockchain): int {
        Sum_{i=0}^{|blockchain| - 1}(
            coinsUsuarioEnBloque(id_usuario, blockhain[i])
        )
    }


    proc agregarBloque (in transacciones: seq<Transaccion>, inout blockchain: BlockChain) {
        requiere {(|transacciones| > 0) ^ (|transacciones| <= 50) ^ (paraTodo i:Z)
             (0 <= i <= |transacciones| - 1) -->
                (esTransaccionValida(transacciones[i]))} // es redundante pero decia que no escatimemos con las verificaciones
        requiere {blockchain = BC_0}
        asegura {|blockchain| = |BC_0| + 1}
        asegura {esBloqueValido(bloque, blockhain)}
        asegura {esBlockChainValida(blockhain)} //redundante

    }


    aux usuariosUnicosEnBloque(in bloque: Bloque): seq<N> {
        (paraTodo i:Z) (0 <= i < |bloque.transacciones| --> IfThenElseFi(bloque.transacciones[i].id_comprador not in res, concat(res, <bloque.transacciones[i].id_comprador>), 
            IfThenElseFi(bloque.transacciones[i].id_vendedor not in res, concat(res(bloque, <bloque.transacciones[i].id_vendedor>), concat(res, < >)))))
    } // VER SI ESTA BIEN

    aux usuariosUnicos(in blockchain: BlockChain): seq<N> {
        // devuelve lista de usuarios
        (paraTodo i:Z) () 

    }

    proc maximosTenedores (in blockchain: BlockChain): seq<N> {
        requiere {|blockchain| > 0}
        requiere {esBlockChainValida(BlockChain)}
        asegura {(paraTodo i:Z) 
                    (0 <= i < |usuariosUnicos(blockchain)|) --> 
                        coinsUsuarioEnCuenta(res[0]) <= coinsUsuarioEnCuenta(usuariosUnicos[i]) } //no hace falta verificar el resto de res xq tienen todos igual plata
    }


    aux cantidadDeTransacciones(in blockchain: BlockChain): int{
        Sum_{i=0}^{|blockhain| - 1} (
           |blockhain[i].transacciones|
        )
    }

    aux cantidadDeCreacion(in blockchain: BlockChain): int{
        IfThenElseFi(|blockhain| > 3000,
        3000,
        |blockhain|)
    }

    aux montoTotalBloque(in bloque: Bloque): int{
        Sum_{i=0}^{|bloque.transacciones| - 1} (
           bloque.transacciones[i].monto
        )
    }

    aux montoTotal(in blockchain: BlockChain): int{
        Sum_{i=0}^{|blockhain| - 1} (
            montoTotalBloque(blockhain[i])
        )
    }

    proc montoMedio(in blockchain: Blockchain): R {
        requiere{esBlockchainValida(blockchain)}
        requiere{|blockchain| > 0}
        asegura{res = (montoTotal(blockchain) - cantidadDeCreacion(blockhain)) / 
        (cantidadDeTransacciones(blockhain) - cantidadDeCreacion(blockhain))}
    }

    proc cotizacionAPesos(in cotizaciones: seq<N>, in blockhain: BlockChain): seq<N> {
        requiere{|cotizaciones| > 0}
        requiere{|cotizaciones| = |blockhain|}
        asegura{
            (paraTodo i: Z, 0 <= i <= |cotizaciones| - 1 ->L res[i] = montoTotalBloque(blockhain[i]) * cotizaciones[i])
        }
    }

   


        
            // proc agregarTransaccion (in id_comprador: int, in id_vendedor: natural, in monto: natural, inout blockchain: BlockChain) {
            //     requiere {id_comprador != id_vendedor}
            //     asegura {transaccionUnica(res[0], blockchain)}
            // }
}
```
