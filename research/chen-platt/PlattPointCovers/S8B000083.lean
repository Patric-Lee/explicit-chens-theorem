import PlattPointSubsetKernel
import PlattPointPackets.S6B000256
import PlattPointPackets.S6B000257
import PlattPointPackets.S6B000258
import PlattPointPackets.S6B000259
import PlattPointPackets.S6B000260
import PlattPointPackets.S6B000261
import PlattPointPackets.S6B000262
import PlattPointPackets.S6B000263
import PlattPointPackets.S6B000264
import PlattPointPackets.S6B000265
import PlattPointPackets.S6B000266
import PlattPointPackets.S6B000267
import PlattPointPackets.S6B000268
import PlattPointPackets.S6B000269
import PlattPointPackets.S6B000270
import PlattGlobalGrid.S8B000083
namespace ChenEffective.PlattWindow.PointCovers.S8B000083
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000256.points ++ ChenEffective.PlattWindow.PointPackets.S6B000257.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000258.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000259.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000260.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000261.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000262.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000263.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000264.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000265.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000266.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000267.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000268.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000269.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000270.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000083.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000083.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000083
