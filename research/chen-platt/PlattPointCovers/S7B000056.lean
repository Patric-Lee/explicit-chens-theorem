import PlattPointSubsetKernel
import PlattPointPackets.S2B000257
import PlattPointPackets.S2B000258
import PlattPointPackets.S2B000259
import PlattPointPackets.S2B000260
import PlattPointPackets.S2B000261
import PlattGlobalGrid.S7B000056
namespace ChenEffective.PlattWindow.PointCovers.S7B000056
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000257.points ++ ChenEffective.PlattWindow.PointPackets.S2B000258.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000259.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000260.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000261.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000056.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000056.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000056
