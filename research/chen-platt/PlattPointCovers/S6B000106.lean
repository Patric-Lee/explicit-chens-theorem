import PlattPointSubsetKernel
import PlattPointPackets.S2B000018
import PlattPointPackets.S2B000019
import PlattPointPackets.S2B000020
import PlattGlobalGrid.S6B000106
namespace ChenEffective.PlattWindow.PointCovers.S6B000106
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S2B000018.points ++ ChenEffective.PlattWindow.PointPackets.S2B000019.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000020.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000106.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000106.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000106
