
module ADPfusion.Core.Apply where

--import Data.Array.Repa.Index
import Data.PrimitiveArray.Index.Class (Z(..), (:.)(..))



-- * Apply function 'f' in '(<<<)'

class Apply x where
  type Fun x :: *
  apply :: Fun x -> x

instance Apply (Z:.a -> res) where
  type Fun (Z:.a -> res) = a -> res
  apply fun (Z:.a) = fun a
  {-# INLINE apply #-}

instance Apply (Z:.a:.b -> res) where
  type Fun (Z:.a:.b -> res) = a->b -> res
  apply fun (Z:.a:.b) = fun a b
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c -> res) where
  type Fun (Z:.a:.b:.c -> res) = a->b->c -> res
  apply fun (Z:.a:.b:.c) = fun a b c
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d -> res) where
  type Fun (Z:.a:.b:.c:.d -> res) = a->b->c->d -> res
  apply fun (Z:.a:.b:.c:.d) = fun a b c d
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e -> res) where
  type Fun (Z:.a:.b:.c:.d:.e -> res) = a->b->c->d->e -> res
  apply fun (Z:.a:.b:.c:.d:.e) = fun a b c d e
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f -> res) = a->b->c->d->e->f -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f) = fun a b c d e f
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g -> res) = a->b->c->d->e->f->g -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g) = fun a b c d e f g
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h -> res) = a->b->c->d->e->f->g->h -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h) = fun a b c d e f g h
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i -> res) = a->b->c->d->e->f->g->h->i -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i) = fun a b c d e f g h i
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j -> res) = a->b->c->d->e->f->g->h->i->j -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j) = fun a b c d e f g h i j
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k -> res) = a->b->c->d->e->f->g->h->i->j->k -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k) = fun a b c d e f g h i j k
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l -> res) = a->b->c->d->e->f->g->h->i->j->k->l -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l) = fun a b c d e f g h i j k l
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m -> res) = a->b->c->d->e->f->g->h->i->j->k->l->m -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m) = fun a b c d e f g h i j k l m
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n -> res) = a->b->c->d->e->f->g->h->i->j->k->l->m->n -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n) = fun a b c d e f g h i j k l m n
  {-# INLINE apply #-}

instance Apply (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n:.o -> res) where
  type Fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n:.o -> res) = a->b->c->d->e->f->g->h->i->j->k->l->m->n->o -> res
  apply fun (Z:.a:.b:.c:.d:.e:.f:.g:.h:.i:.j:.k:.l:.m:.n:.o) = fun a b c d e f g h i j k l m n o
  {-# INLINE apply #-}

