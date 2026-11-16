import PlattPointSubsetKernel
import PlattPointPackets.S2B000023
import PlattPointPackets.S2B000024
import PlattPointPackets.S2B000025
import PlattPointPackets.S2B000026
import PlattGlobalGrid.S6B000108
namespace ChenEffective.PlattWindow.PointCovers.S6B000108
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000023.points ++ ChenEffective.PlattWindow.PointPackets.S2B000024.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000025.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000026.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000108.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000108.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000108
