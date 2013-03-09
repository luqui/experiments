import System.Random
import qualified Data.List as List
import Control.Applicative

-- helper functions that take in StdGen and return (Result,new StdGen)
plum_radius :: StdGen -> (Float,StdGen)
plum_radius = randomR (0,1)
unitpoint   :: Float -> StdGen -> ((Float,Float,Float),StdGen)
unitpoint f g = 
    let (x,g') = randomR (0,f) g
        (x',g'') = randomR (0,f) g'
        (x'',g''') = randomR (0,f) g''
    in ((x,x',x''), g'')
plum_speed  :: Float -> StdGen -> (Float,StdGen)
plum_speed f = randomR (0,f)

-- The overall calculation of the value
plum_point  :: StdGen -> (((Float,Float,Float),(Float,Float,Float)),StdGen)
plum_point gen  = (((px,py,pz),(vx,vy,vz)),gen_out)
  where
    (r, gen2)         = plum_radius gen
    ((px,py,pz),gen3) = unitpoint r gen2
    (s, gen4)         = plum_speed r gen3
    ((vx,vy,vz),gen5) = unitpoint s gen4
    gen_out           = gen5

-- Turning it into some kind of list
plum_data_list  :: StdGen -> Int -> (((Float,Float,Float),(Float,Float,Float)),StdGen)
plum_data_list seed_gen 0  = plum_point seed_gen
plum_data_list seed_gen i  = plum_point gen2
  where
    (_,gen2)  = plum_data_list seed_gen (i-1)

results n = do
    gen <- getStdGen
    return $ map (plum_data_list gen) [1..n]

sumPoint ((x,y,z),(x',y',z')) = x+y+z+x'+y'+z'

-- Getting 100 results
main = do
  gen <- getStdGen
  let data_list = map (plum_data_list gen) [1..1000]
  putStrLn $ List.intercalate " " (map show data_list)
