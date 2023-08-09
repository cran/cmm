\name{EVS}
\alias{EVS}
\docType{data}
\title{European Values Study (EVS): attitude towards women's role in society}
\description{
European Values Study 1999/2000, Views on Women's Roles.

The data are tabulated in Bergsma, Croon, and Hagenaars (2009, Table 5.1a). 
Section 5.1.2 in Bergsma, Croon and Hagenaars (2009).
}
\usage{data(EVS)}
\format{
  A data frame with 960 observations on the following variables.
  \describe{
    \item{\code{S}}{Sex (factor):
        1 = Male;
        2 = Female.
       }
    \item{\code{A}}{Date of Birth (ordered):
        1 = Before 1945;
        2 = 1945-1963;
        3 = After 1963.
       }
    \item{\code{E}}{Level of education (ordered):
        1 = Lower;
        2 = Intermediate;
        3 = Higher.
       }
    \item{\code{R}}{Religion (ordered):
        1 = Religious person;
        2 = Not a religious person;
        3 = Convinced atheist.
       }
    \item{\code{W}}{Attitude women's role in society (factor):
        1 = Traditional;
        2 = Nontraditional.
       }
  }
}

\source{
European Values Study 1999/2000
}
\references{

 Bergsma, W. P., Croon, M. A., & Hagenaars, J. A. P. (2009).
 \emph{Marginal models for dependent, clustered, and longitudinal categorical data.}
 New York: Springer.

}

\examples{
data(EVS)

# Table SAERW
var = c("S", "A", "E", "R", "W");
dim = c(2, 3, 3, 3, 2);

# matrices for table SA
at1 <- MarginalMatrix(var, c("S", "A"), dim);
bt1 <- ConstraintMatrix(c("S", "A"), list(c("S"), c("A")), c(2, 3));

# matrices for table SAER
at2 <- MarginalMatrix(var, c("S", "A", "E", "R"), dim);
bt2 <- ConstraintMatrix(var = c("S", "A", "E", "R"), 
                       suffconfigs = list(c("S", "A", "E"), c("S", "R"), c("A", "R")), 
                       dim = c(2, 3, 3, 3));

# matrices for table SAERW: constraints
at3 <- MarginalMatrix(var, c("S", "A", "E", "R", "W"), dim);
bt3 <- ConstraintMatrix(var = c("S", "A", "E", "R", "W"), 
 suffconfigs = list(c("S", "A", "E", "R"), c("S", "W"), c("A", "W"), c("E", "W"), c("R", "W")), 
 dim = c(2, 3, 3, 3, 2))

# matrix for table SAERW: design matrix
x <- DesignMatrix(var = c("S", "A", "E", "R", "W"), 
 suffconfigs = list(c("S", "A", "E", "R"), c("S", "W"), c("A", "W"), c("E", "W"), c("R", "W")), 
 dim = c(2, 3, 3, 3, 2));

# model1: specification using only constraints
at <- rbind(at1, at2, at3);
bt <- DirectSum(bt1, bt2);
bt <- DirectSum(bt, bt3);
model1 <- list(bt, "log", at);

# model2: same as model1 but using both constraints and a design matrix 
# to specify a loglinear model for the joint distribution
at <- rbind(at1, at2);
bt <- DirectSum(bt1, bt2);
model2 <- list(list(bt, "log", at), x);

nkps3 <- MarginalModelFit(EVS, model2, MaxError = 10.^-25,
    MaxSteps = 1000,
    ShowProgress = 10,
    MaxStepSize = .3 );
}
\keyword{datasets}
