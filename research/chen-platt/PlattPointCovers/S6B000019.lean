import PlattPointSubsetKernel
import PlattPointPackets.S1B000350
import PlattPointPackets.S1B000351
import PlattPointPackets.S1B000352
import PlattPointPackets.S1B000353
import PlattGlobalGrid.S6B000019
namespace ChenEffective.PlattWindow.PointCovers.S6B000019
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000350.points ++ ChenEffective.PlattWindow.PointPackets.S1B000351.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000352.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000353.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000019.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000019.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000019
