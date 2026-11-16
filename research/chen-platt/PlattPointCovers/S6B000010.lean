import PlattPointSubsetKernel
import PlattPointPackets.S1B000327
import PlattPointPackets.S1B000328
import PlattPointPackets.S1B000329
import PlattGlobalGrid.S6B000010
namespace ChenEffective.PlattWindow.PointCovers.S6B000010
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000327.points ++ ChenEffective.PlattWindow.PointPackets.S1B000328.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000329.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000010.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000010.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000010
