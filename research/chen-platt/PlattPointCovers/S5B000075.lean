import PlattPointSubsetKernel
import PlattPointPackets.S1B000221
import PlattPointPackets.S1B000222
import PlattPointPackets.S1B000223
import PlattGlobalGrid.S5B000075
namespace ChenEffective.PlattWindow.PointCovers.S5B000075
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000221.points ++ ChenEffective.PlattWindow.PointPackets.S1B000222.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000223.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000075.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000075.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000075
