# source("h:/my documents/r files/cmm.r")
#
# R programme for the book:
#
# Marginal models
# Models for Dependent, Clustered, and Longitudinal Categorical Data
# www.cmm.st
# 
# Wicher P. Bergsm
# Marcel Croon
# Jacques A. Hagenaars
#
# Springer, Statistics for the Social Sciences
#
# This R-programme is written by Wicher Bergsma and Andries van der Ark, 2009
#
#
##############################################################################
##############################################################################
##############################################################################
#
# List of main functions
#
#   Fitting:
#
#       MarginalModelFit( n, model ) (TO DO: Method="MDI")
#       SampleStatistics( n, coeff ) 
#       ModelStatistics( n, m, model, coeff )
#
#   Matrix functions:
#
#       MarginalMatrix( var, marg, dim )
#       DesignMatrix( var, marg, dim )
#       ConstraintMatrix( var, marg, dim )
#       DirectSum( mat1, mat2 )
# 
#
#   Specification of coefficients and models
#
#       SpecifyCoefficient( name, parameters, rep )  (TO DO: "KendallTau" etc)
#       JoinModels( model1, model2 )
#
#
#   Data formatting:
# 
#       RecordsToFrequencies( rec, dim )
# 
##############################################################################
##############################################################################
##############################################################################
# libraries: matrix operations
# for the nullspace function
library(MASS)
# ?Null






##############################################################################
##############################################################################
##############################################################################
# matrix functions: desmat,MarginalMatrix


##############################################################################
# DirectSum (from web)
DirectSum <- function (m1, m2, p.tr = 0, p.ll = 0)
{
     ## p.tr and p.ll are padding values
     topleft <- m1
     topright <- matrix(p.tr, nrow(m1), ncol(m2))
     colnames(topright) <- colnames(m2)
     lowleft <- matrix(p.ll, nrow(m2), ncol(m1))
     lowright <- m2
     rbind(cbind(topleft, topright), cbind(lowleft, lowright))
} 



##############################################################################
#subsets

#a recursive function returning a list of all subsets of size n of list elements.
#used for function allsubsets
allnsubsets1<-function(x,n,index=1){
   rtn<-list()
   if(length(x)<n){return(NULL)}
   if(length(x)==n){return(list(x))}
   if(length(x)>n){
      #trigger recursion
      for(i in 1:length(x)){
         if(i>=index){
            rtn<-c(rtn,allnsubsets1(x[-i],n,i))
         }
      }   
   }
   return(rtn)
} 
allnsubsets=function(x,n,index=1){rev(allnsubsets1(x,n,index))}

#allnsubsets(c(1,2,3,4),2)


#finds all subsets of a set or a list of sets
allsubsets1 <- function(x){
   if ( data.class(x) == "NULL" ) { subsets <- c() }
   else
   if (data.class(x)=="numeric" || data.class(x)=="character"){
      n=length(x)
      subsets=allnsubsets(x,1)
      if (n>1) for(i in 2:n) subsets=c(subsets,allnsubsets(x,i))
   }
   else{
      subsets=allsubsets1(x[[1]])
      k=length(x)
      if (k>1) for(i in 2:k) subsets=union(subsets,allsubsets1(x[[i]]))
   }
   return(subsets)
} 

allsubsets = function(x){c("NULL",allsubsets1(x))}

#allsubsets(list(c(1,2),c(2,3)))

#allsubsets(c(1,2,3))
#allsubsets(list(c(1,2,3)))
#allsubsets(list(c(1,2),c(2,3),c(1,4)))




##############################################################################
#MarginalMatrix and DesignMatrix


desmat1 = function(var, subvar, dim, coding ){

   #(*lmat2 produces kxk-matrix*)
   lmat2 = function(type,k){
      x = c(1:k) - mean(c(1:k));
      switch( type,
         "Identity"  = diag(k),
         "Nominal"   = rbind(diag(k)[1:k-1,]),
         "Linear"    = rbind(x),
         "Quadratic" = rbind(x,c(1:k)^2),
         "Cubic"     = rbind(x,c(1:k)^2,c(1:k)^3),
         "Quartic"   = rbind(x,c(1:k)^2,c(1:k)^3,c(1:k)^4),
         "Quintic"   = rbind(x,c(1:k)^2,c(1:k)^3,c(1:k)^4,c(1:k)^5)
         )
   }
   
   nvar=length(var);
   coding = if( is.character(coding)&&length(coding)==1 ) rep(coding,length(subvar)) else coding;
   coding = lapply( var, function(x){if(is.element(x,subvar)) coding[subvar==x][[1]] else rbind(rep(1,dim[var==x]))} );

   matlist = list();
   for(i in 1:nvar){
      matlist[[i]] = 
         if      (is.vector(coding[[i]])&&!is.character(coding[[i]])) rbind(coding[[i]])
         else if (is.matrix(coding[[i]])&&!is.character(coding[[i]])) coding[[i]]
         else if (is.element(var[[i]],subvar))                        lmat2(coding[[i]],dim[[i]])
         else                                                         rbind(rep(1,dim[[i]]))
   }
   mat=matlist[[1]];
   if(nvar>1) for (i in 2:nvar){mat = kronecker(mat,matlist[[i]])}

   return(t(mat))
}

#desmat1(c(1,2),c(1,2),c(3,3),c("Nominal","Quintic"))
#desmat1(c(1,2),c(1,2),c(3,3),list("Nominal",rbind(c(1,2,3))))
#desmat1(c(1,2),c(1,2),c(3,3),c("Nominal","Quintic"))
#desmat1(c("A","B"),c("A","B"),c(3,3),c("Nominal","Quintic"))
#desmat1(c("A","B"),c(),c(2,2),c("Nominal"))
#desmat1(c("A"),c("A"),c(2),c("Nominal"))


DesignMatrix = function(var, suffconfigs, dim, SubsetCoding="Automatic", MakeSubsets=TRUE){

   suffconfigs = if(is.list(suffconfigs)) suffconfigs else list(suffconfigs)
   marglist = if(MakeSubsets) allsubsets(suffconfigs) else suffconfigs;
   nmarg=length(marglist);
   
   #put in standard form
   q = SubsetCoding[[1]];
   SubsetCoding = if( is.character(q) || is.numeric(q) ) list(SubsetCoding) else SubsetCoding

   nsubs = length(SubsetCoding);

   #coding gives specification for each marginal
   coding = 
      if( isTRUE(SubsetCoding=="Automatic") ) rep("Nominal",nmarg)   
      else if( is.character(SubsetCoding[[1]]) && length(SubsetCoding)==1 && length(SubsetCoding[[1]])==1) rep(SubsetCoding,nmarg) 
      else lapply(marglist, function(x){ 
         for(i in 1:nsubs) {
            ss1 = SubsetCoding[[i]][[1]];
            if(length(x)==length(ss1)) if(isTRUE(prod(x==ss1)==1)) return(SubsetCoding[[i]][[2]])
            }
         return("Nominal")
         }  )
   deslist = list();
   for(i in 1:nmarg) deslist[[i]] = desmat1(var,marglist[[i]],dim,coding[[i]])
   des = deslist[[1]];
   if(nmarg>1) for(i in 2:nmarg) des = cbind(des,deslist[[i]])
   return(des)
}
#DesignMatrix(c("P", "R"), list(c("P","R")), c(3,3), SubsetCoding = list(c("P", "R"),list("Linear", rbind(c(1,1,0),c(1,1,0),c(0,0,1)))))
#DesignMatrix(c("P", "R"), list(c("P","R")), c(3,3), SubsetCoding = list(c("P", "R"),list("Linear", rbind(c(1,1,0),c(1,1,0),c(0,0,1)))))
#DesignMatrix(c("A","B"),list(c("A"),c("B")),c(2,2))
#DesignMatrix(c(1,2,3),list(c(1,2),c(2,3)),c(3,3,3),SubsetCoding=list(list(c(1,2),c("Linear","Linear")),list(c(1,2),c("Linear","Linear"))))
#t(DesignMatrix(c(1,2),c(1,2),c(3,3),SubsetCoding="Identity",MakeSubsets=FALSE))

MarginalMatrix = function(var,marg,dim,SubsetCoding="Identity"){
   t(DesignMatrix(var,marg,dim,SubsetCoding=SubsetCoding,MakeSubsets=FALSE))
}
#MarginalMatrix(c(1,2),list(c(1),c(2)),c(3,3))

new.null <- function (M) {
   tmp <- qr(M)
   set <- if (tmp$rank == 0) 1:ncol(M) else -(1:tmp$rank)
   qr.Q(tmp, complete = TRUE)[, set, drop = FALSE]
}


#returns hierarchical model constraint matrix, ie nullspace of design matrix
ConstraintMatrix = function(var,suffconfigs,dim, SubsetCoding="Automatic"){
   return(t(new.null(DesignMatrix(var,suffconfigs,dim,SubsetCoding))))
   }

#ConstraintMatrix(c(1,2),list(c(1),c(2)),c(2,2))

 













#compute the matrix for obtaining the beta parameters under different coding schemes

betamat = function(var, subvar, dim, coding){

   #lmat1 produces kx1-vector, lmat2 produces kxk-matrix

   polmat = function(x,k){
      powmat = rbind(rep(1,k));
      if(k>1) for(i in 1:(k-1)) powmat = rbind(powmat, x^i - mean(x^i))
      invmat = solve(t(powmat))
      return(rbind(invmat[2:k,],rep(0,k)))     }
   
   lmat1 = function(type2, k){
      x = if(length(type2)>1) type2[[2]] else NULL
      type = if(length(type2)>1) type2[[1]] else type2 #second arg is constant for dummy coding, vector for polynomial
      switch( type,
         "Effect"     = rbind(rep(1/k,k)),
         "Simple"     = rbind(rep(1,k)),
         "Dummy"      = {if(length(x)==0) x=1; rbind(diag(k)[x,])}, 
         "Polynomial" = rbind(rep(1,k))
      ) }  

   lmat2 = function(type2,k){
      x = if(length(type2)>1) type2[[2]] else NULL
      type = if(length(type2)>1) type2[[1]] else type2 #second arg is constant for dummy coding, vector for polynomial
      switch( type,
         "Effect"     = diag(k)-1/k,
         "Simple"     = diag(k),
         "Dummy"      = {if(length(x)==0) x=1; diag(k) - t(matrix(rep(diag(k)[x,],k),k,k))},
         "Polynomial" = {if(length(x)==0) x=c(1:k)-(k+1)/2; polmat(x,k)}
         ) }
         
   nvar = length(var);
   coding = if( is.character(coding)&&length(coding)==1 ) as.list(rep(coding,nvar)) else coding;

   matlist = list();
   for( i in 1:nvar ){ matlist[[i]] = if(is.element(var[[i]],subvar)) lmat2(coding[[i]],dim[[i]]) else lmat1(coding[[i]],dim[[i]]) }

   mat = matlist[[1]] 
   if(nvar==1) mat else for(i in 2:nvar) mat = kronecker(mat,matlist[[i]])

   return(mat)

   }

#betamat(c(1,2),c(1,2),c(2,2),list(list("Dummy",2),"Effect"))
#betamat(c(1,2),c(1,2),c(3,3),"Effect")
#betamat(c(1,2),c(1,2),c(2,2),list(list("Polynomial",c(-2,2)),"Polynomial"))


#   
#   lmat2["Polynomial", k_] := 
#   lmat2[{"Polynomial", Range[k] - (k + 1)/2}, k];

























###############################################################################################
###############################################################################################
###############################################################################################
# specification of coefficients


#probabilities in honogeneous form
spec.prob <- function(dim){
  k = prod(dim);
  id <- diag(rep(1,k))
  one <- t(rep(1,k))
  m1 <- rbind(id,one)
  m2 <- t(rbind(id,-one))
  matlist <- list(id,m2,m1)
  funlist <- list("exp","log","identity")
  coeff <- list(matlist, funlist)
  return(coeff)
}

#log probabilities in honogeneous form
spec.logprob <- function(dim){
  k = prod(dim);
  id <- diag(rep(1,k))
  one <- t(rep(1,k))
  m1 <- rbind(id,one)
  m2 <- t(rbind(id,-one))
  matlist <- list(m2,m1)
  funlist <- list("log","identity")
  coeff <- list(matlist, funlist)
  return(coeff)
}


spec.condprob <- function(z){
  var = z[[1]];
  condvar = z[[2]];
  dim = z[[3]];
  ident = diag(prod(dim));
  at1 = MarginalMatrix(var,condvar,dim);
  at1 = t(at1) %*% at1;
  at1 = rbind(ident,at1);
  at2 = cbind(ident,-ident);
  at3 = ident;
  matlist = list(at3, at2, at1);
  funlist = list("exp", "log", "identity");
  list(matlist, funlist)
}
  
#spec.condprob(list(c(1,2),c(1),c(2,2)))



spec.mean <- function(scores){
   at <- t(matrix(scores))
   prob <- spec.prob(length(scores))
   matlist <- c(list(at), prob[[1]])
   funlist <- c(list("identity"), prob[[2]])
   coeff <- list(matlist, funlist)
   return(coeff)
}


spec.ginimeandifference <- function(scores){
   k <- length(scores)
   q=diag(k)
   m1=matrix(nrow=k^2,ncol=k)
   for(i in 1:k) for(j in 1:k) m1[(i-1)*k + j,] = q[i,] + q[j,]
   m2=matrix(nrow=1,ncol=k^2)
   for(i in 1:k) for(j in 1:k) m2[,(i-1)*k + j] = abs(scores[i] - scores[j])
   prob <- spec.prob(k)
   matlist <- c( list( m2, m1 ), prob[[1]] )
   funlist <- c(list( "exp", "log" ), prob[[2]])
   coeff <- list(matlist, funlist)
   return(coeff)
}

spec.entropy <- function(k){
   at <- t(matrix(rep(1,k)))
   prob <- spec.prob(k)
   matlist <- c(list(at), prob[[1]])
   funlist <- c(list("xlogx"), prob[[2]])
   coeff <- list(matlist, funlist)
   return(coeff)
}


spec.diversityindex <- function(k){
   at <- t(matrix(rep(1,k)))
   prob <- spec.prob(k)
   matlist <- c(list(at), prob[[1]])
   funlist <- c(list("xbarx"), prob[[2]])
   coeff <- list(matlist, funlist)
   return(coeff)
}


spec.variance <- function(scores){
   newscores <- scores - min(scores) + 1
   m1 <- rbind(newscores^2, newscores, rep(1,length(scores)))
   m2 <- rbind(c(1, 0, -1),c(0, 2, -2))
   m3 <- t(matrix(c(1,-1)))
   matlist <- list(m3, m2, m1)
   funlist <- list("exp", "log", "identity")
   coeff <- list(matlist, funlist)
   return(coeff)
}

spec.standarddeviation <- function(scores){
   varspec <- spec.variance(scores)
   m1 <- t(matrix(c(1)))
   matlist <- c(list(m1), varspec[[1]])
   funlist <- c(list("sqrt"), varspec[[2]])
   coeff <- list(matlist, funlist)
   return(coeff)
}

#coeff=spec.standarddeviation(c(1,2))
#gfunction(c(2,2),coeff)

spec.covariance <- function(xyscores){
   xscores <- xyscores[[1]]
   xscores <- xscores - min(xscores) + 1
   yscores <- xyscores[[2]]
   yscores <- yscores - min(yscores) + 1
   k <- length( xscores )
   l <- length( yscores )
   m1a <- MarginalMatrix( c(1,2), list(c(1,2),c(1),c(2)), c(k,l) )
   m1b1 <- as.vector( as.vector(xscores) %o% as.vector(yscores) )
   m1b1 <- rbind( rep( 1, k*l ), m1b1 )
   m1b2 <- DirectSum( rbind(xscores), rbind(yscores) )
   m1b <- DirectSum( m1b1, m1b2 )
   m1 <- m1b %*% m1a
   m2 <- rbind(c(1, 1, 0, 0),c(0, 0, 1, 1))
   m3 <- t(matrix(c(1,-1)))
   matlist <- list(m3, m2, m1)
   funlist <- list("exp", "log", "identity")
   list(matlist, funlist)
}

   
spec.correlation <- function(xyscores){
   xscores <- xyscores[[1]]
   xscores <- xscores - min(xscores) + 1
   yscores <- xyscores[[2]]
   yscores <- yscores - min(yscores) + 1
   k <- length( xscores )
   l <- length( yscores )
   m1a <- MarginalMatrix( c(1,2), list(c(1,2),c(1),c(2)), c(k,l) )
   m1b1 <- as.vector( as.vector(xscores) %o% as.vector(yscores) )
   m1b1 <- rbind( rep( 1, k*l ), m1b1 )
   m1b2 <- DirectSum( rbind(xscores,xscores^2), rbind(yscores,yscores^2) )
   m1b <- DirectSum( m1b1, m1b2 )
   m1 <- m1b %*% m1a
   m2 <- rbind(c(1, 1, 0, 0, 0, 0), c(0, 0, 1, 0, 1, 0), c(0, 0, 0, 1, 0, 0), c(0, 0, 2, 0, 0, 0), c(0, 0, 0, 0, 0, 1), c(0, 0, 0, 0, 2, 0) )
   m3 <- rbind( c(1, 0, 0, 0, 0, 0), c(0, 1, 0, 0, 0, 0), c(0, 0, 1, 0, -1, 0), c(0, 0, 0, 1, 0, -1) )
   m4 <- rbind( c(1, 0, -.5, -.5), c(0, 1, -.5, -.5) )
   m5 <- rbind( c(1, -1) )
   matlist <- list( m5, m4, m3, m2, m1 )
   funlist <- list( "exp", "log", "exp", "log", "identity" )
   list(matlist, funlist)
}

#SpecifyCoefficient("Correlation",list(c(1,2),c(1,2)))

spec.diffprop <- function(c,Response="Columns",DropLast=FALSE){
   id1 <- diag(c)
   id2 <- diag(2*c)
   
   m1b = if(Response == "Columns") MarginalMatrix(c(1, 2), c(1), c(2,c)) else MarginalMatrix(c(1, 2), c(2), c(c,2))
   m1b = t(m1b) %*% m1b;
   m1 = rbind(id2, m1b);

   m2 = cbind(id2, -id2);
   m3 = cbind(id1, -id1);
   m3 = if(DropLast) m3[1:dim(m3)[1]-1,] else m3
   list( list(m3, m2, m1), list("exp", "log", "identity"))
}

#spec.diffprop(2,Response="Rows",DropLast=TRUE)

spec.goodmankruskaltau <- function(rc,Response="Columns"){
   r=rc[[1]];
   c=rc[[2]];

   id = diag(r*c);
   idc = diag(c);
  
   m1a = MarginalMatrix(c(1,2),c(1),c(r,c))
   m1b = MarginalMatrix(c(1,2),c(2),c(r,c))
   m1 = if(Response=="Columns") rbind(id,t(m1a) %*% m1a,m1b) else rbind(id,t(m1b) %*% m1b,m1a)

   z1=matrix(0,r*c,c);
   z2=matrix(0,r*c,r*c);
   m2 = rbind(cbind(2*id, -id, z1), cbind(id, z2, z1), cbind(t(z1), t(z1), 2*idc));

   m3a = matrix(1,1,r*c);
   m3b = matrix(1,1,c);
   zero= matrix(0,1,r*c);
   m3 = rbind(cbind(m3a, zero, -m3b), cbind(zero, m3a, -m3b));

   m4 = matrix(c(1,-1),nrow=1,ncol=2);
   m5 = matrix(c(1),nrow=1,ncol=1);

   funlist = list("exp", "log", "exp", "log", "identity");
   matlist = list(m5, m4, m3, m2, m1);

   prob <- spec.prob(r*c)
   matlist <- c(matlist, prob[[1]])
   funlist <- c(funlist, prob[[2]])
   coeff <- list(matlist, funlist)
   return(coeff)
}

#coeff=spec.goodmankruskaltau(3,2)
#gfunction(c(4,2,6,4,6,7),coeff)


spec.uncertaintycoefficient <- function(rc){
   r=rc[[1]];
   c=rc[[2]];

   m1 = MarginalMatrix(c(1,2),list(c(1, 2),c(1),c(2)), c(r,c));
   m2rc = matrix(1,1,r*c);
   m2r = matrix(1,1,r);
   m2c = matrix(1,1,c);
   zrc= matrix(0,1,r*c);
   zr = matrix(0,1,r);
   m2 = rbind(cbind(m2rc, -m2r, -m2c), cbind(zrc, zr, -m2c));
   m3 = matrix(c(1,-1),nrow=1,ncol=2);
   m4 = matrix(c(1),nrow=1,ncol=1);

   funlist = list("exp","log","xlogx","identity");
   matlist = list(m4, m3, m2, m1);

   prob <- spec.prob(r*c)
   matlist <- c(matlist, prob[[1]])
   funlist <- c(funlist, prob[[2]])
   coeff <- list(matlist, funlist)
   return(coeff)
}


spec.cohenkappa <- function(k){
   m1a = c(diag(k));
   m1b = MarginalMatrix(c(1,2), list(c(),c(1),c(2)), c(k,k));
   m1one = matrix(1,1,k*k);
   m1 = rbind(m1a, m1b, m1one);
   m2a = DirectSum(DirectSum(matrix(1,1,1),matrix(1,1,1)),MarginalMatrix(c(1,2),c(2),c(2,k)));
   m2b = apply(m2a,1,sum);
   m2 = cbind(m2a,-m2b);
   m3 = DirectSum(matrix(1,1,1), rbind(c(0,rep(1, k)), c(1,rep(-1, k))));
   m4 = rbind(c(1, 0, -1), c(0, 1, -1));
   m5 = matrix(c(1,-1),nrow=1,ncol=2);
   list(list(m5, m4, m3, m2, m1),list("exp","log","exp","log","identity"))
}

#coeff=spec.cohenkappa(2)
#gfunction(c(4,2,6,4),coeff)


spec.concdiscprobs <- function(rc){
   r=rc[[1]];
   c=rc[[2]];

   m1a=matrix(0,(r-1)*(c-1),r*c);
   m1b=matrix(0,(r-1)*(c-1),r*c);
   m1c=matrix(0,(r-1)*(c-1),r*c);
   m1d=matrix(0,(r-1)*(c-1),r*c);
   for(i in 1:(r-1)) for(j in 1:(c-1)) for(k in (i+1):r) for(l in (j+1):c) {m1a[[(i-1)*(c-1)+j,(k-1)*c+l]]=1}
   for(i in 1:(r-1)) for(j in 1:(c-1)) for(k in (i+1):r) for(l in (j+1):c) {m1b[[(i-1)*(c-1)+j,(i-1)*c+j]]=1}
   for(i in 1:(r-1)) for(j in 2:c) for(k in (i+1):r) for(l in 1:(j-1)) {m1c[[(i-1)*(c-1)+j-1,(k-1)*c+l]]=1}
   for(i in 1:(r-1)) for(j in 2:c) for(k in (i+1):r) for(l in 1:(j-1)) {m1d[[(i-1)*(c-1)+j-1,(i-1)*c+j]]=1}
   m1 = rbind(m1a, m1b, m1c, m1d);
   m2 = diag((r-1)*(c-1));
   m2 = cbind(m2, m2);
   m2 = DirectSum(m2, m2);
   m3 = rbind(4 * rep(1,(r-1)*(c-1)));
   m3 = DirectSum(m3, m3);
   funlist = list("exp","log","identity");
   matlist = list(m3, m2, m1);

   prob <- spec.prob(r*c)
   matlist <- c(matlist, prob[[1]])
   funlist <- c(funlist, prob[[2]])
   coeff <- list(matlist, funlist)
   return(coeff)
}

#coeff=spec.concdiscprobs(2,3)
#gfunction(c(4,2,6,4,6,7),coeff)


spec.kendalltau <- function(rc){
   concdiscspec <- spec.concdiscprobs(rc)
   m1 = matrix(c(1,-1),nrow=1,ncol=2);
   matlist <- c(list(m1), concdiscspec[[1]])
   funlist <- c(list("identity"), concdiscspec[[2]])
   coeff <- list(matlist, funlist)
   return(coeff)
}

spec.gamma <- function(rc){

   m1 = rbind(c(1, 0), c(0, 1), c(1, 1));
   m2 = rbind(c(1, 0, -1), c(0, 1, -1));
   m3 = rbind(c(1, -1));

   funlist = list("exp","log","identity");
   matlist = list(m3, m2, m1);

   concdiscspec <- spec.concdiscprobs(rc)
   matlist <- c(matlist, concdiscspec[[1]])
   funlist <- c(funlist, concdiscspec[[2]])
   coeff <- list(matlist, funlist)
   return(coeff)
}

#coeff=spec.gamma(2,3)
#gfunction(c(4,2,6,4,6,7),coeff)

spec.loglinearpars = function(z){
   if(length(z)==2&&!is.numeric(z)) 
      {dim = z[[1]]; coding = z[[2]]}
   else 
      {dim = z; coding = "Effect"}
   var = c(1:length(dim));
   mat = betamat(var, var, dim, coding)
   list(list(mat),list("log"))
}

#spec.loglinearpars(list(c(2,2),"Dummy"))
#spec.loglinearpars(c(2,2))


spec.logOR <- function(z){
   list(list(rbind(c(1,-1,-1,1))),list(c("log")))
}


MultiCoefficient <- function(coeff,k){
    if( k == 1 ) newcoeff <- coeff
    else{
        matlist <- coeff[[1]] 
        funlist <- coeff[[2]]
        q <- length(matlist)
        newmatlist <- list()
        for (i in 1:q) {
            newmatlist[[i]] <- matlist[[i]]
            for (j in 2:k) newmatlist[[i]] <- DirectSum(newmatlist[[i]],matlist[[i]])   } 
        newcoeff <- list( newmatlist, funlist) }
    return(newcoeff)
}


SpecifyCoefficient <- function(name,arg,rep=1){
    z = arg;
    coeff <- switch( name,
        "Mean" = spec.mean(z),
        "Variance" = spec.variance(z),
        "StandardDeviation" = spec.variance(z),
        "Entropy" = spec.entropy(z),
        "DiversityIndex" = spec.diversityindex(z),
        "GiniMeanDifference" = spec.ginimeandifference(z),
        "Covariance" = spec.covariance(z),
        "Correlation" = spec.correlation(z),
        "CohenKappa" = spec.cohenkappa(z), 
        "KendallTau" = spec.kendalltau(z),
        "GoodmanKruskalGamma" = spec.gamma(z),
        "DifferenceInProportions" = spec.diffprop(z), #z has the form (var,condvar,dim)
        "ConditionalProbabilities" = spec.condprob(z),
        "Probabilities" = spec.prob(z),
        "LogProbabilities" = spec.logprob(z),
        "LoglinearParameters" = spec.loglinearpars(z), #z=dim
        "LogOddsRatio" = spec.logOR(z)
        )
    MultiCoefficient(coeff,rep)
}


JoinModels <- function(model1,model2){

  model1 = tomodelform(model1);
  model2 = tomodelform(model2);

  bt1 = model1[[1]][[1]]
  matlist1 = model1[[1]][[2]][[1]]
  funlist1 = model1[[1]][[2]][[2]]
  at1 = model1[[1]][[3]]
  x1 = model1[[2]]

  bt2 = model2[[1]][[1]]
  matlist2 = model2[[1]][[2]][[1]]
  funlist2 = model2[[1]][[2]][[2]]
  at2 = model2[[1]][[3]]
  x2 = model2[[2]]

  bt = DirectSum(bt1,bt2)
  matlist = list();
  for(i in 1:length(matlist1)) matlist[[i]] = DirectSum(matlist1[[i]],matlist2[[i]])
  funlist = if( length(funlist1)==length(funlist2) && funlist1[[1]]==funlist2[[1]] ) funlist1 else break;
  at = rbind(at1,at2)
  model = list(bt,list(matlist,funlist),at);
  
  return(model)

}


###############################################################################################
###############################################################################################
###############################################################################################
# Misc functions (Andries)


#simplification using ftable
RecordsToFrequencies <- function(data){ c(t(ftable(data))) }

#dat=rbind(c(1,1,2),c(2,1,3))
#RecordsToFrequencies(dat,c(2,2),SelectColumns=c(1,2))
#RecordsToFrequencies(dat,c(2,2,3))


# 4. Required functions
Gfunction <- function( m, coeff ){
# requires functions (1) phi, (2) dphi,
  matlist <- coeff[[1]]      # read design matrices from the model
  funlist <- coeff[[2]]     # read algebraic operations from the model
  q <- length(funlist)
  g <- list()
  g[["g.0"]] <- m
  for (i in 1:q) g[[i+1]] <- phi(matlist[[q+1-i]], g[[i]], funlist[[q+1-i]])
  Gfun <- list()
  Gfun[["Gfun.0"]] <- diag(length(m))
  for (i in 1:q) Gfun[[i+1]] <- dphi(matlist[[q+1-i]], g[[i]], Gfun[[i]], funlist[[q+1-i]])
  return( Gfun[[q+1]] )
}

gfunction <- function(m,coeff){
# requires functions (1) phi
    matlist <- coeff[[1]]     # read design matrices from the model
    funlist <- coeff[[2]]     # read algebraic operations from the model
    q <- length(funlist)
    g <- list()
    g[["g.0"]] <- m
    for (i in 1:q) g[[i+1]] <- phi(matlist[[q+1-i]], g[[i]], funlist[[q+1-i]])
    return( g[[q+1]] )
}

phi <- function(A,f, action){
# Numerical values are translations h(A %*% f) = A %*% f -
    eps=1E-80;
    switch(action,
    "identity" = A %*% f,
    "exp"      = A %*% exp(f),
    "log"      = A %*% log(abs(f)+eps),
    "sqrt"     = A %*% sqrt(f),
    "xlogx"    = A %*% (-f*log(f+eps)),
    "xbarx"    = A %*% (f*(1-f))  # x(1-x)
    )
}

dphi <- function(A,f,df, action){
  eps=1E-80;
  switch(action,
  "identity" = A %*% df,
  "exp"      = A %*% (as.numeric(exp(f)) * df),
  "log"      = A %*% (as.numeric(1/(f+eps)) * df),
  "sqrt"     = A %*% (as.numeric(1/(2*sqrt(f))) * df),
  "xlogx"    = A %*% (as.numeric(-1-log(f+eps)) * df),
  "xbarx"    = A %*% (as.numeric(1-2*f) * df),  # x(1-x)
  )
}

pds <- function(n,m,lambda=1){
# Power divergence statistics (Cressie + Read)
   if(length(m)!=length(n))stop("m and n have unequal lengths")
   n[n < 1e-100] <- 1e-100
   m[m < 1e-100] <- 1e-100
   if(lambda==0) return(2*sum(n*log(n/m)))
   if(lambda==-1) return(2*sum(m*log(m/n)))
   return(2/(lambda*(lambda+1))*sum(n*(((n/m)^lambda) - 1)))
}



###############################################################################################
###############################################################################################
###############################################################################################
# Printing statistics


printalgorithmdetails = function(time,ite,convcrit){
   cat("Time taken            = ",time," seconds","\n")
   cat("Number of iterations  = ",ite,"\n") 
   cat("Convergence criterion = ",convcrit,"\n")
}


printbasicstatistics = function(n,m,df,eig,showeig){
   df = df[1]+df[2];
   g2 = pds(n,m,0)
   x2 = pds(n,m,1)
   bic=g2-df*log(sum(n))
   pval=signif(1-pchisq(g2,df),5)
   cat("G^2         = ",g2,"\n")
   cat("df          = ",df,"\n")
   cat("p-value     = ",pval,"\n")
   cat("Sample size = ",sum(n),"\n")
   cat("X^2         = ",x2,"\n")
   cat("BIC         = ",bic,"\n")
   if(showeig) {cat("\n"); cat("Eigenvalues of inverse covariance matrix of Lagrange multipliers: ", "\n", eig, "\n")}
}

printadvancedstatistics = function( obsval, fitval, covtheta, covresid, coeffdim, catlabels, satmod=FALSE, ShowCorrelations=FALSE ){

    var <- diag(covtheta)
    fitval[abs(fitval) < 1e-20] <- 0
    var[var <= 0] <- 1e-80
    se <- sqrt(var)
    zscores <- fitval / se
    vr <- diag(covresid);
    vr[vr <= 0] <- 1e-80
    adjres <- if(satmod) 0 else (obsval - fitval)/sqrt(vr)

    se[se < 1e-39] <- 0
    zscores[abs(zscores) < 1e-39] <- 0
    adjres[abs(adjres) < 1e-39] <- 0

    cormat = if(length(se)==1) 1 else diag(1/se) %*% covtheta %*% diag(1/se)
    
    coeffdim  = rev(coeffdim);
    catlabels = rev(catlabels);

    nvar=length(coeffdim)
    if(nvar==1) {  
       if(!satmod) {
          cat("   Observed values             = ",obsval,sep="\t","\n")
          cat("   Fitted values               = ",fitval,sep="\t","\n");
          cat("   Ese of fitted values        = ",se,sep="\t","\n");
          cat("   Fitted values / std errors  = ",zscores,sep="\t","\n");
          cat("   Adjusted residuals          = ",adjres,sep="\t","\n") }
       else{
          cat("   Observed values              = ",obsval,sep="\t","\n")
          cat("   Ese of observed values       = ",se,sep="\t","\n");
          cat("   Observed values / std errors = ",zscores,sep="\t","\n")} }
    else {    
#       catlabels=vector("list",nvar)  #labels for categories
#       for(i in 1:nvar){ 
#          for(j in 1:coeffdim[[i]]) {catlabels[[i]][[j]]=
#             if(is.list(varlabels[[i]])) paste(varlabels[[i]][[1]],"=",varlabels[[i]][[2]][[j]],sep="")
#             else paste(varlabels[[i]],"=",j,sep="")}}
       if(!satmod) {
          cat("   Observed values: ","\n");  print(array(obsval,coeffdim,dimnames=catlabels))
          cat("   Fitted values: ","\n");  print(array(fitval,coeffdim,dimnames=catlabels))
          cat("   Ese of fitted values: ","\n");  print(array(se,coeffdim,dimnames=catlabels))
          cat("   Fitted values / std errors: ","\n");  print(array(zscores,coeffdim,dimnames=catlabels))
          cat("   Adjusted residuals: ","\n");  print(array(adjres,coeffdim,dimnames=catlabels))  }
       else{
          cat("   Observed values: ","\n");  print(array(obsval,coeffdim,dimnames=catlabels))
          cat("   Ese of observed values: ","\n");  print(array(se,coeffdim,dimnames=catlabels))
          cat("   Observed values / std errors: ","\n");  print(array(zscores,coeffdim,dimnames=catlabels)) }
    }

    if(ShowCorrelations && length(se)>1) {
       cat("Correlation matrix:","\n")
       cat(cormat,"\n","\n") }
}


tocatlabels = function(lab,dim){
   nvar = length(dim);
   catlabels=vector("list",nvar)  #labels for categories
   for(i in 1:nvar){ 
       for(j in 1:dim[[i]]) {catlabels[[i]][[j]]=
          if(is.list(lab[[i]])) paste(lab[[i]][[1]],"=",lab[[i]][[2]][[j]],sep="")
          else paste(lab[[i]],"=",j,sep="")}}
   catlabels
   }

#tocatlabels(c(1,2),c(2,2))
#tocatlabels(list(list("G",c("men","women")),"T"),c(2,3))


printThetaAndBeta = function(obsval, fitval, covtheta, covresid, coeffdim, varlabels, showcoeffs, showpars,satmod=FALSE, ShowCorrelations=FALSE,modeltype="Manifest",ParameterCoding="Effect"){

   coeffdim  = if(isTRUE(coeffdim=="Automatic")) c(length(obsval)) else coeffdim;
   nvar=length(coeffdim)
   varlabels = if(isTRUE(varlabels=="Automatic")) apply(rbind(c(1:nvar)),1,function(x){paste("Var",x,sep="")}) else varlabels;
   catlabels=tocatlabels(varlabels,coeffdim);

   varlabels1 = list();   #varlabels1 contains only variable labels, not category labels
   for(i in 1:nvar){ varlabels1[[i]] = if(is.list(varlabels[[i]])) varlabels[[i]][[1]] else varlabels[[i]] }
   varlabels1 = as.character(varlabels1)


   if(showcoeffs){
      cat("Statistics for the coefficients: ", "\n")
      cat("Variables = ",varlabels1," (dim = ",coeffdim,")","\n",sep="")
      printadvancedstatistics(obsval, fitval, covtheta, covresid, coeffdim, catlabels, satmod=satmod, ShowCorrelations=ShowCorrelations)
   }

   printBeta = function(efflab,effcatlab,effdim,obsval,fitval,covtheta,covresid,coeffdim,varlabels,ParameterCoding="Effect"){
      effmat = betamat(varlabels,efflab,coeffdim,ParameterCoding);
      obsval2   = effmat %*% obsval;
      fitval2   = effmat %*% fitval
      covtheta2 = effmat %*% covtheta %*% t(effmat)
      covresid2 = if(satmod) 0 else effmat %*% covresid %*% t(effmat)
      cat("Effect = ");cat(as.character(efflab,sep=","),sep=",");cat(" (dim = ");cat(effdim,sep=",");cat(")","\n",sep="")
      printadvancedstatistics(obsval2, fitval2, covtheta2, covresid2, effdim, effcatlab, satmod=satmod, ShowCorrelations=ShowCorrelations)  
   }

   if(showpars){
      cat("\n")
      cat("Statistics for the parameters: ", "\n")
      subvar = allsubsets(c(1:nvar));
      for(i in 1:length(subvar)) printBeta(varlabels1[subvar[[i]]],catlabels[subvar[[i]]],coeffdim[subvar[[i]]],obsval,fitval,covtheta,covresid,coeffdim,varlabels1,ParameterCoding=ParameterCoding)
   }

}


###############################################################################################
###############################################################################################
###############################################################################################
# Fitting procedures

margmodfit = function(n, model, 
    PrintStatistics=TRUE,
    MaxSteps=1000,MaxError=1e-25,StartingPoint="Automatic",MaxInnerSteps=2,ShowProgress=TRUE,CoefficientDimensions="Automatic",Labels="Automatic",
    ShowCoefficients=TRUE,ShowParameters=FALSE, ShowCorrelations=FALSE, Title="", ParameterCoding="Effect", MaxStepSize=1){

    eps= 10e-80;
    starttime = proc.time()[3]

    bt    <- model[[1]][[1]]
    coeff <- model[[1]][[2]]
    at    <- model[[1]][[3]]    
    d     <- model[[1]][[4]]    
    x     <- model[[2]]
        
    step <- 1             # Initial step size (no modification yet)
    k <- 0                # index for iterations k = 1, 2, .... . k = 1 is initial iterration
    w <- list()
    H <- matrix()

    m  <- if(isTRUE(StartingPoint=="Automatic") && !is.matrix(x) ){ n + 1e-3 } 
          else if(is.matrix(x)) rep(sum(n)/length(n),length(n))
          else StartingPoint        # initial estimates for expected frequencies
    m  <- as.numeric(m)
    logm <- log(m)                      # logarithm of initial expected frequencies
    atm  <- if(data.class(at)!="matrix") m else at %*% m
    g  <- matrix(gfunction(atm,coeff))  # initial values of g in a C x 1 vector
    Gt <- if(data.class(at)!="matrix") Gfunction(atm,coeff) else Gfunction(atm,coeff) %*% at   # initial values of G in an L x C matrix
    h  <- bt %*% g - d
    Ht <- bt %*% Gt
    H  <- t(Ht)
    df <- nrow(bt)                      # number of constraints
    mu <- matrix(0,df,1)                # initial estimates of Lagrange multipliers in a C x 1 vector
    error <- 100000                     # initial values of error

    if(!isTRUE(!ShowProgress)) cat("Iteration      ","G^2             ","Error","\n")

    # Iteration = 1, ..., k
    repeat{
        k <- k + 1
        atm <- if(data.class(at)!="matrix") m else at %*% m
        g <- gfunction(atm,coeff)
        Gt <- if(data.class(at)!="matrix") Gfunction(atm,coeff) else Gfunction(atm,coeff) %*% at
        h <- bt %*% g - d
        Ht <- (bt %*% Gt )
        H <- t(Ht)
        HDH <- Ht %*% ( m * H )
        lambda <- - solve( HDH, Ht %*% (n - m) + h )
        loglinincr = if(isTRUE(x=="None")) 0 else x %*% (solve(t(x) %*% (m * x)) %*% (t(x) %*% (n - m))) - (n + eps)/(m + eps) + 1
        incr <- (n - m)/m + H %*% lambda + loglinincr
        logm <- logm + MaxStepSize*incr
        m <- exp(logm)
        m <- as.numeric(m)
        m[m < 1e-80] <- 1e-80
        error <-  t(incr) %*% (m * incr)
        if( isTRUE(ShowProgress) || (data.class(ShowProgress)=="numeric" && isTRUE(k%%ShowProgress==0)) ){ cat(k,"             ",pds(n,m,0),"         ",error,"\n") }
        if ( k >= MaxSteps || abs(error) < MaxError ) break
    }

    endtime <- proc.time()[3]

    if(PrintStatistics){
        print(Title)
        cat("\n")
        printalgorithmdetails(endtime-starttime,k,error)
        cat("\n")
        coeff = model[[1]][2:3]
        ModelStatistics(n, m, model, coeff, CoefficientDimensions=CoefficientDimensions, Labels=Labels, 
           ShowCoefficients=ShowCoefficients,ShowParameters=ShowParameters, ShowCorrelations=ShowCorrelations, ParameterCoding=ParameterCoding )
    }
    
    return(m)
}


margmodfitEM <- function( n, latdim, model, MaxOuterSteps=1000, MaxError=1e-20, MaxInnerSteps=2, ShowProgress=TRUE,CoefficientDimensions="Automatic",Labels="Automatic",
     ShowCoefficients=TRUE,ShowParameters=FALSE, ShowCorrelations=FALSE, Title="", MaxStepSize=1, ParameterCoding="Effect"){

    starttime = proc.time()[3]
    eps <- 1e-80
    k <- 0
    collapse = function(q){ apply( matrix( q, nrow = latdim ), 2, sum ) }
    expand = function(q){ rep(q, each=latdim ) }
    v <- c(1:(length(n)*latdim))
    mhat = expand(n/latdim)
    mhat = mhat + sum(n)/100/length(mhat)  #startingpoint

    cat("Iteration      ","G^2             ","Error","\n")

    repeat{ k <- k + 1
        nhat <- mhat * expand( (n+eps) / (collapse(mhat)+eps) ) # E-step
        newmhat <- margmodfit( nhat, model, MaxSteps=MaxInnerSteps, StartingPoint=mhat, ShowProgress=FALSE, PrintStatistics=FALSE, MaxStepSize=MaxStepSize )  # M-step
        error <- sum( abs( mhat - newmhat ) )
        mhat <- newmhat
        cat("  ",k,"             ",pds(nhat,newmhat,0),"         ",error,"\n")
        if ( k >= MaxOuterSteps || abs(error) < MaxError ) break
    }

    endtime <- proc.time()[3]

    print(Title)
    cat("\n")
    printalgorithmdetails(endtime-starttime,k,error)
    cat("\n")
    coeff = model[[1]][2:3]
    ModelStatistics(n, mhat, model, coeff, CoefficientDimensions=CoefficientDimensions, Labels=Labels, ShowCoefficients=ShowCoefficients,
       ShowParameters=ShowParameters, ShowCorrelations=ShowCorrelations, ParameterCoding=ParameterCoding )

    return(mhat)
}


gsk <- function( n, model, CoefficientDimensions="Automatic", Labels="Automatic", Title="" ){

    model = tomodelform(model)
    bt    <- model[[1]][[1]]
    coeff <- model[[1]][[2]]
    at    <- model[[1]][[3]]    
    d     <- model[[1]][[4]]    
    x     <- model[[2]]

    atn <- if(data.class(at)!="matrix") n else at %*% n

    h  <- bt %*% gfunction(atn,coeff) - d
    Gt <- if(data.class(at)!="matrix") Gfunction(atn,coeff) else Gfunction(atn,coeff) %*% at
    Ht <- (bt %*% Gt )

    H <- t(Ht)
    a <- t(at)
    G <- t(Gt)
    H <- t(Ht)

    GDG <- Gt %*% (n * G) 
    GDH <- Gt %*% (n * H)
    HDH <- Ht %*% (n * H)
    
    df <- length(h)
    waldstat <- h %*% solve( HDH, h )
    bic <- waldstat - df * log( sum(n) )
    pval <- signif(1-pchisq(waldstat,df),5)
    eig = eigen( HDH, only.value = T )$values;

    print(Title)
    cat("\n")
    cat("Wald statistic = ",waldstat,"\n")
    cat("df             = ",df,"\n")
    cat("p-value        = ",pval,"\n")
    cat("Sample size    = ",sum(n),"\n")
    cat("BIC            = ",bic,"\n")
    cat("Eigenvalues: ",eig,"\n")

    covresid <- GDH %*% solve(HDH) %*% t(GDH) 
    covtheta <- GDG - covresid
    obsval <- gfunction(atn,coeff)
    fitval <- covtheta %*% solve( GDG, obsval )

    printadvancedstatistics( obsval, fitval, covtheta, covresid, CoefficientDimensions, Labels )
}


#puts marginal model into standard form (bt,theta,at,d)
tomargmodform = function(margmodel){

   #case 0: margmodel=None
   if( isTRUE(margmodel == "None") ) return(margmodel)

   #find out if d is given in model, if so, drop it from margmodel
   if({lm =length(margmodel);is.vector(margmodel[[lm]])&&is.numeric(margmodel[[lm]])&&!is.matrix(margmodel)}){
         d = margmodel[[lm]];
         margmodel = margmodel[-lm]
         }
   else d = "None";
      
   margmodel = 
   
   #case 1: single matrix is given
   if( data.class(margmodel)=="matrix" ){
      at = margmodel;
      id = diag(nrow(at));
      bt = diag(nrow(at));
      list( bt, list( list(id), list("identity") ), at)
   }
   
   #case 2: form is {bt,Log,at}
   else if(length(margmodel) == 3 && data.class(margmodel[[2]])=="character"){
      bt = margmodel[[1]];
      at = margmodel[[3]];
      if(ncol(bt)!=nrow(at)) {cat("Incompatible matrix dimensions in model specification",dim(bt),"and",dim(at),"\n");break;};
      coeff = list( list(diag(ncol(bt))),list(margmodel[[2]]) );
      list(bt, coeff, at)
   }
   
   #case 3: form is standard: {bt,coeff,at}, with coeff={matlist,funlist}
   else if(length(margmodel) == 3 && !data.class(margmodel[[2]])=="character" ) margmodel
   
   #hereafter: length[margmodel]=2 ################################
   
   #form is eg {Log,at}
   else if(data.class(margmodel[[1]])=="character" && data.class(margmodel[[2]])=="matrix"){id=diag(nrow(margmodel[[2]]));list(id,list(list(id),list(margmodel[[1]])),margmodel[[2]])}

   #form is {bt,Log}
   else if(data.class(margmodel[[2]])=="character" && data.class(margmodel[[1]])=="matrix"){id=diag(ncol(margmodel[[1]]));list(margmodel[[1]],list(list(id),list(margmodel[[2]])),id)}

   
   #form is {bt,coeff}
   else if( data.class(margmodel[[1]])=="matrix" && length(margmodel[[2]]) == 2 ) list( margmodel[[1]], margmodel[[2]], "None" )
   
   #form is {coeff,None}
   else if( isTRUE(margmodel[[2]] == "None") && length(margmodel[[1]]) == 2 ){
      coeff = margmodel[[1]];
      df = nrow((coeff[[1]][[1]]));
      bt = diag(df);
      list( bt, coeff, "None" )
   } 
   
   #form is {coeff,at}
   else if( data.class(margmodel[[2]])=="matrix" && length(margmodel[[1]]) == 2 ){
      coeff = margmodel[[1]];
      at = margmodel[[2]];
      df = nrow((coeff[[1]][[1]]));
      bt = diag(df);
      list( bt, coeff, at )
   }
   
   #form is coeff with coeff={matlist,funlist}
   else if( length(margmodel) == 2 && data.class(margmodel[[1]][[1]])=="matrix" && data.class(margmodel[[2]])=="list" ){
      coeff = margmodel;
      df = nrow((coeff[[1]][[1]]));
      bt = diag(df);
      list( bt, coeff, "None" )
   }
   
   else{ cat("Cannot recognize model specification", margmodel); break}

   #now homogenize margmodel specification
   matlist = margmodel[[2]][[1]];
   funlist = margmodel[[2]][[2]];
   k = ncol(matlist[[length(matlist)]]);
   prob <- spec.prob(k);
   matlist <- c(matlist, prob[[1]]);
   funlist <- c(funlist, prob[[2]]);
   coeff <- list(matlist, funlist);
   margmodel[[2]] = coeff;
   #add a constant vector d
   d = if( isTRUE(d=="None") ) rep(0,nrow(margmodel[[1]])) else d;
   margmodel[[4]] = d

   #check if matrix dimensions are correct
   dim0 = list(c(0,length(d)));
   dimfirst = list(dim(margmodel[[1]]));
   dimlast  = list(dim(margmodel[[3]]));
   dimlist  = lapply(margmodel[[2]][[1]],dim);
   dimlist  = append(dimlist,dimfirst,after=0);
   dimlist  = append(dimlist,dim0,after=0);
   dimlist  = if(length(dimlast[[1]])>0) append(dimlist,dimlast) else dimlist
   for(i in 2:length(dimlist)){if(dimlist[[i-1]][[2]]!=dimlist[[i]][[1]]){print("Incompatible matrix dimensions. Dimensions are: ");print(dimlist);stop()}}
   
   return(margmodel)
}

#mod=list(matrix(1:6,2,3),"log",matrix(1:12,3,4),c(1,2))
#tomargmodform(mod)

#margmodel="None"
#tomargmodform(margmodel)
#margmodel=rbind(c(1,2))
#margmodel=list( rbind(c(1,2)), "log", rbind(c(1,2)) )
#tomodelform(margmodel)



#puts model into standard form: (margmodel,x) where x denotes design matrix for loglinear model for full table
tomodelform = function(model){

   desmatQ = function(mat){ if( !(data.class(mat)=="matrix") ) FALSE else if(nrow(mat)>ncol(mat)) TRUE else FALSE }
  
   standardformmodel =
  
      if(desmatQ(model)) list("None",model)                                                    #form is model=x
  
      else if( isTRUE(model[[1]]=="None") && desmatQ(model[[2]]) ) model                       #form is model={None,x}
     
      else if( length(model)==2 && desmatQ(model[[2]]) && data.class(model[[1]])=="character" ){   #form is eg {Log,x}: only used for coefficients, no df for margmod
         x = model[[2]]
         id = diag(nrow(x))
         list( tomargmodform(list(id,list(list(id),list(model[[1]])), "None")), x )}
        
      else if( length(model) == 2 && (desmatQ(model[[2]]) || isTRUE(model[[2]] == "None") ) ){ #form is {margmodel,x} or {margmodel,None}
         margmod = tomargmodform(model[[1]])
         x = model[[2]]
         list(margmod, x)}
        
      else list(tomargmodform(model), "None")                                                  #form is "margmod", no design matrix
      
   return(standardformmodel)
}

#x=rbind(c(1,2))
#tomodelform(x)

modeldf = function(model,n){
   tblsize = tablesize(model);
   latdim = tblsize / length(n)
   margmod = model[[1]];
   x = model[[2]];
   df1 = if (isTRUE(margmod == "None")) 0 else nrow(margmod[[1]])
   df2 = if (isTRUE(x == "None")) 0 else max(0, tblsize/latdim - ncol(x));
   c(df1,df2)
   }

tablesize = function(model) {
   if(length(model)==2){
      if      (!isTRUE(model[[2]] == "None")) nrow(model[[2]])
      else if (!isTRUE(model[[1]][[3]] == "None")) ncol(model[[1]][[3]])
      else    {k=length(model[[1]][[2]][[1]]); ncol(model[[1]][[2]][[1]][[k]])}  }
   else 
      if(isTRUE(model[[3]]=="None")){k=length(model[[2]][[1]]); ncol(model[[2]][[1]][[k]])}
      else ncol(model[[3]])
}

#mod=list(matrix(1:2,2,2),"log",matrix(1:6,2,3))
#mod=list(matrix(1:2,2,2),"log","None")
#mod2=tomargmodform(mod)
#tablesize(mod2)


MarginalModelFit = function(dat, model, MaxSteps=1000, MaxStepSize=1, MaxError=1e-20, StartingPoint="Automatic", MaxInnerSteps=2, ShowProgress=TRUE, CoefficientDimensions="Automatic",
    Labels="Automatic",ShowCoefficients=TRUE,ShowParameters=FALSE, ParameterCoding="Effect", ShowCorrelations=FALSE, Method="ML", Title="" ){

#    n   = if(data.class(n)=="numeric") n else {dim = 1 + apply(n,2,max) - apply(n,2,min); RecordsToFrequencies(n)};
    n  = if(data.class(dat)=="numeric") dat else c(t(ftable(dat)));
    model = tomodelform(model); #put model in standard form: "list(margmod,x)"
    latdim = tablesize(model) / length(n)

    switch( Method, 
        "ML" = 
            if      ( latdim != floor(latdim) )  cat("Error: unable to determine latent dimension","\n") 
            else if ( latdim == 1 )              margmodfit( n, model, MaxSteps=MaxSteps, MaxStepSize=MaxStepSize, StartingPoint=StartingPoint, MaxInnerSteps=MaxInnerSteps, ShowProgress=ShowProgress, 
                                                    ShowCoefficients=ShowCoefficients, ShowParameters=ShowParameters, Labels=Labels, CoefficientDimensions=CoefficientDimensions, Title=Title, ParameterCoding=ParameterCoding )
            else                                 margmodfitEM( n, latdim, model, MaxOuterSteps=MaxSteps, MaxInnerSteps=MaxInnerSteps, MaxError=MaxError, Title=Title, ParameterCoding=ParameterCoding ),
        "GSK" = gsk( n, model, Title=Title ) 
    )
}

SampleStatistics = function(dat, coeff, CoefficientDimensions="Automatic",
    Labels="Automatic", ShowCoefficients=TRUE, ShowParameters=FALSE, ParameterCoding="Effect", ShowCorrelations=FALSE,  Title="" ){

    eps <- 10e-80

    n   = if(data.class(dat)=="numeric") dat else c(t(ftable(dat)));
    coeff2 = tomargmodform(coeff); #yields list(bt,coeff,at)
    bt = coeff2[[1]];
    coeff = coeff2[[2]];
    coeff[[1]] = c(list(bt),coeff[[1]]);
    coeff[[2]] = c(list("identity"),coeff[[2]]);
    at = coeff2[[3]];

    atn <- if(data.class(at)!="matrix") n else at %*% n
    Gt <- if(data.class(at)!="matrix") Gfunction( atn, coeff ) else  Gfunction( atn, coeff ) %*% at 
    GDG <- Gt %*% (n * t(Gt))

    print(Title)
    cat("Sample size = ",sum(n),"\n")
    eig = eigen( GDG, only.value = T )$values;
    cat("Eigenvalues sample covariance matrix","\n")
    cat("\t",eig,"\n")

    covresid <- 0
    covtheta <- GDG
    obsval = gfunction( atn + eps, coeff )
    cat("\n")
    printThetaAndBeta( obsval, obsval, covtheta, covresid, CoefficientDimensions, Labels, ShowCoefficients, ShowParameters, satmod=TRUE, ShowCorrelations=ShowCorrelations, ParameterCoding=ParameterCoding )
}


# model has standard form
# coeffplus has the same form as model

ModelStatistics <- function(dat, fitfreq, model, coeff, CoefficientDimensions="Automatic",
    Labels="Automatic",ShowCoefficients=TRUE,ShowParameters=FALSE,Method="ML", ParameterCoding="Effect", ShowCorrelations=FALSE, Title="" ){
    eps = 10.^-80

    mhat = fitfreq;
    n   = if(data.class(dat)=="numeric") dat else c(t(ftable(dat)));
    model = tomodelform(model); #put model in standard form: "list(margmod,x)"
    coeffplus = tomargmodform(coeff); #yields list(bt,coeff,at,d)

    bt2    = coeffplus[[1]];
    coeff2 = coeffplus[[2]];
    at2    = coeffplus[[3]];
    coeff2[[1]] = c(list(bt2),coeff2[[1]]);
    coeff2[[2]] = c(list("identity"),coeff2[[2]]);
    bt2    = diag(nrow(bt2));

    bt     = model[[1]][[1]];
    coeff  = model[[1]][[2]];
    at     = model[[1]][[3]];   
    x      = model[[2]];

    latdim = length(mhat) / length(n);
    collapse = function(q){ apply( matrix( q, nrow = latdim ), 2, sum ) }
    expand = function(q){ rep(q, each=latdim ) }
    nhat <- if(latdim==1) n else mhat * expand( (n+eps) / (collapse(mhat)+eps) ) 
    manmhat = if(latdim == 1) mhat else collapse(mhat);

    Gt <- if(data.class(at2)!="matrix") bt2 %*% Gfunction( mhat, coeff2 ) else bt2 %*% Gfunction( at2 %*% mhat, coeff2 ) %*% at2
    Ht <- if(data.class(at)!="matrix")  bt  %*% Gfunction( mhat, coeff )  else bt  %*% Gfunction( at  %*% mhat, coeff )  %*% at
    obsval <- if(data.class(at)!="matrix") gfunction( nhat, coeff2) else gfunction( at %*% nhat, coeff2)
    fitval <- if(data.class(at)!="matrix") gfunction( mhat, coeff2) else gfunction( at %*% mhat, coeff2)

    GDG <- Gt %*% (mhat * t(Gt)) 
    GDH <- Gt %*% (mhat * t(Ht))
    HDH <- Ht %*% (mhat * t(Ht))
    covresid <- GDH %*% solve(HDH) %*% t(GDH) 
    covtheta <- GDG - covresid
    eig = eigen( HDH, only.value = T )$values;
    df = modeldf(model,n)
    print(Title)
    printbasicstatistics(n,manmhat,df,eig,TRUE)
    cat("\n")

    modeltype = if(latdim==1) "Manifest" else "Latent"
    printThetaAndBeta( obsval, fitval, covtheta, covresid, CoefficientDimensions, Labels, ShowCoefficients, ShowParameters, ShowCorrelations=ShowCorrelations, modeltype=modeltype, ParameterCoding=ParameterCoding )
}



######################################################
#OLD

#effectmat = function(dim){ 
#   var = c(1:length(dim))
#   subvar = allsubsets(var)
#   MarginalMatrix(var, subvar, dim, Contrasts=TRUE)
#}


#margmat01 = function(marg,dim,Contrasts=FALSE,DropLast=FALSE){
#returns a matrix which produces appropriate marginals when multiplied with probability vector
#marg has 0s and 1s indicating which marginals are needed
#dim gives the dimension of each variable

#   if ( data.class(marg) == "NULL" ) { mat <- rbind(rep(1,prod(dim)))/(if(Contrasts) prod(dim) else 1) }
#   else
#   if(data.class(marg)=="numeric" || data.class(marg)=="character"){
#      q=list()
#      nvar=length(dim)
#      for (i in 1:nvar){
#         if(marg[[i]]==1) {
#            q[[i]] <- (diag(dim[[i]])-if(Contrasts)1/dim[[i]] else 0) 
#            if(DropLast)q[[i]]=q[[i]][,1:(dim[[i]]-1)]} 
#         else q[[i]] <- matrix(1,dim[[i]]) / (if(Contrasts) dim[[i]] else 1) }
#      mat=q[[1]]
#      if(nvar>1) for (i in 2:nvar){mat<-kronecker(mat,q[[i]])}
#      mat=t(mat)
#      }
#   else{
#      nmarg=length(marg)
#      mat=margmat01(marg[[1]],dim,Contrasts=Contrasts,DropLast=DropLast)
#      if(nmarg>1) for(i in 2:nmarg){
#         mat=rbind(mat,margmat01(marg[[i]],dim,Contrasts=Contrasts,DropLast=DropLast))
#         }
#      }
#   return(mat)
#}

#margmat01(c(1,0),c(3,3),Contrasts=FALSE,DropLast=FALSE)


#MarginalMatrix <- function(var,marg,dim,Contrasts=FALSE,DropLast=FALSE){
#   marg01 = marg
#   if( data.class(marg)=="numeric" || data.class(marg)=="character"){
#      for(i in 1:length(var)){
#         if(is.element(var[[i]],marg)) marg01[[i]]=1 else marg01[[i]]=0
#      }
#   }
#   else{ if(data.class(marg) != "NULL"){
#      for(j in 1:length(marg)){
#         for(i in 1:length(var)){
#            if(is.element(var[[i]],marg[[j]])) marg01[[j]][[i]]=1 else marg01[[j]][[i]]=0
#         }
#      }}
#   }
#   margmat01(marg01,dim,Contrasts=Contrasts,DropLast=DropLast)
#}

#MarginalMatrix(c(1,2),list(c(1,2)),c(2,2),DropLast=TRUE)
#MarginalMatrix(c(1,2),c(),c(2,2))

#margmat01(c(0,0,0),c(2,3,4))
#margmat01(list(c(1,0,0),c(0,1,0),c(0,0,1)),c(2,2,3))
