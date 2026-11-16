import PlattPointSubsetKernel
import PlattPointPackets.S2B000007
import PlattPointPackets.S2B000008
import PlattPointPackets.S2B000009
import PlattPointPackets.S2B000010
import PlattGlobalGrid.S6B000102
namespace ChenEffective.PlattWindow.PointCovers.S6B000102
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000007.points ++ ChenEffective.PlattWindow.PointPackets.S2B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000009.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000010.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000102.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000102.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000102
