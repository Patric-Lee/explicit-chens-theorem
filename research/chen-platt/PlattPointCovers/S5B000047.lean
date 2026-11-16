import PlattPointSubsetKernel
import PlattPointPackets.S1B000180
import PlattPointPackets.S1B000181
import PlattPointPackets.S1B000182
import PlattGlobalGrid.S5B000047
namespace ChenEffective.PlattWindow.PointCovers.S5B000047
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000180.points ++ ChenEffective.PlattWindow.PointPackets.S1B000181.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000182.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000047.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000047.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000047
