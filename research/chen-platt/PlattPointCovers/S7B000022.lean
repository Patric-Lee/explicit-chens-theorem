import PlattPointSubsetKernel
import PlattPointPackets.S2B000120
import PlattPointPackets.S2B000121
import PlattPointPackets.S2B000122
import PlattPointPackets.S2B000123
import PlattGlobalGrid.S7B000022
namespace ChenEffective.PlattWindow.PointCovers.S7B000022
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000120.points ++ ChenEffective.PlattWindow.PointPackets.S2B000121.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000122.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000123.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000022.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000022.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000022
