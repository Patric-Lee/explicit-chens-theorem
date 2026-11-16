import PlattPointSubsetKernel
import PlattPointPackets.S1B000461
import PlattPointPackets.S1B000462
import PlattPointPackets.S1B000463
import PlattPointPackets.S1B000464
import PlattGlobalGrid.S6B000055
namespace ChenEffective.PlattWindow.PointCovers.S6B000055
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000461.points ++ ChenEffective.PlattWindow.PointPackets.S1B000462.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000463.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000464.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000055.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000055.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000055
