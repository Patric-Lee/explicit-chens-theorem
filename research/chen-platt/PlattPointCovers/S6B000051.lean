import PlattPointSubsetKernel
import PlattPointPackets.S1B000447
import PlattPointPackets.S1B000448
import PlattPointPackets.S1B000449
import PlattPointPackets.S1B000450
import PlattGlobalGrid.S6B000051
namespace ChenEffective.PlattWindow.PointCovers.S6B000051
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000447.points ++ ChenEffective.PlattWindow.PointPackets.S1B000448.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000449.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000450.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000051.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000051.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000051
