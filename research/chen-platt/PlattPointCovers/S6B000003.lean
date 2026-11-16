import PlattPointSubsetKernel
import PlattPointPackets.S1B000310
import PlattPointPackets.S1B000311
import PlattPointPackets.S1B000312
import PlattGlobalGrid.S6B000003
namespace ChenEffective.PlattWindow.PointCovers.S6B000003
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000310.points ++ ChenEffective.PlattWindow.PointPackets.S1B000311.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000312.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000003.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000003.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000003
