\name{MarginalMatrix}
\alias{MarginalMatrix}
\title{MarginalMatrix}

\description{Returns marginal matrix; i.e., matrix required to obtained marginal frequencies}

\usage{MarginalMatrix(var, marg, dim, SubsetCoding = "Identity", vec = NULL)}

\arguments{
\item{var}{character or numeric vector containing variables}
\item{marg}{list of character or numeric indicating marginals}
\item{dim}{numeric vector indicating the dimension of \code{var}}
\item{SubsetCoding}{allows a (character) type or a matrix to be assigned to variables for each element of \code{suffconfigs},
see examples and \code{DesignMatrix}}
\item{vec}{Vector containing the observed frequencies of all observed cells and possibly some cells with frequency equal to zero. 
           The rownames of \code{vec} must equal the score patterns associated with the cells. 
           \code{vec} is typically created using \code{RecordsToFrequencies}, and allows maximum empirical maximum likelihood estimation or 
           empirical likelihood estimation of CMMs; two estimation methods that do no require the evaluation of all cells that are useful if 
           the number of score patterns  is large.} 
}

\details{
Gives the matrix which, multiplied by a probability vector, gives the marginal probabilities.
The probability vector is assumed to be a vectorized form of the probabilities in a table, such that the last variable changes value fastest,
then the before last variable, etc. For example, the cells of a \eqn{2 \times 3}{2 x 3} table are arranged in vector form as (11,12,13,21,22,23).
To achieve this, the appropriate way to vectorize a data frame \code{dat} is using \code{c(t(ftable(dat)))}.

Special case of transposed \code{DesignMatrix}:
\preformatted{
 MarginalMatrix <- function(var,marg,dim,SubsetCoding="Identity")
 t(DesignMatrix(var,marg,dim,SubsetCoding=SubsetCoding,MakeSubsets=FALSE))
}
Allows weighted sums of probabilities using \code{SubsetCoding}

}


\value{
 matrix
}

\references{
  Bergsma, W. P. (1997).
  \emph{Marginal models for categorical data}.
  Tilburg, The Netherlands: Tilburg University Press.
  \url{http://stats.lse.ac.uk/bergsma/pdf/bergsma_phdthesis.pdf}

  Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
  Marginal models for dependent, clustered, and longitudunal categorical data.
  Berlin: Springer.
  
  Van der Ark, L. A., Bergsma, W. P., & Koopman L. (2023)
  Maximum augmented empirical likelihood estimation of categorical marginal models for large sparse contingency tables. 
  Paper submitted for publication.
}


\author{
 W. P. Bergsma \email{w.p.bergsma@lse.ac.uk}
}

\seealso{
\code{\link{ConstraintMatrix}}, \code{\link{DesignMatrix}}, \code{\link{DirectSum}}, \code{\link{RecordsToFrequencies}}, \code{\link{Margins}}
}

\examples{
# Computing marginal frequencies
n <- c(1:6)  #example list of frequencies
var <- c("A","B")
marg <- list(c("A"),c("B"))
dim <- c(2,3)
at <- MarginalMatrix(var,marg,dim)
# list of marginal frequencies:
at %*% n

# identitymatrix: several ways of specifying:
marg <- c("A","B")
MarginalMatrix(var, marg,dim)
MarginalMatrix(var, marg, dim,
 SubsetCoding = list(c("A", "B"), list("Identity", "Identity")))
MarginalMatrix(var, marg, dim,
 SubsetCoding = list(c("A","B"), list(rbind(c(1,0),c(0,1)), rbind(c(1,0,0),c(0,1,0),c(0,0,1)))))

# omit second category of first variable
at <- MarginalMatrix(var, marg, dim,
 SubsetCoding = list(c("A","B"), list(rbind(c(1,0)),"Identity")))
at %*% n

# Example of maximum augmented empirical likelihood (MAEL) estimation 
data(acl)
dat <- acl[, 1:2] + 1                                 # select 2 items from ACL 
var <- 1 : ncol(dat)                                  # define the variables
marg <- Margins(var, c(0, 1))                         # margins are total (0) and 1st order 
dim <- rep(5, length(var))
n.obs <- RecordsToFrequencies(dat, var, dim, "obs")   # frequency vector with observed cells
t(n.obs)
n.1k  <- RecordsToFrequencies(dat, var, dim, "1k")    # frequency vector with observed and
                                                      # some unobserved cells
t(n.1k)
at.obs <- MarginalMatrix(var, marg, dim, vec = n.obs) # marginal matrix based on n.obs 
at.obs
at.1k  <- MarginalMatrix(var, marg, dim, vec = n.1k)  # marginal matrix based on n.1k
at.1k
}

\keyword{univar}
