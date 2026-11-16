import PlattPointSubsetKernel
import PlattPointPackets.S1B000324
import PlattPointPackets.S1B000325
import PlattPointPackets.S1B000326
import PlattPointPackets.S1B000327
import PlattGlobalGrid.S6B000009
namespace ChenEffective.PlattWindow.PointCovers.S6B000009
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000324.points ++ ChenEffective.PlattWindow.PointPackets.S1B000325.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000326.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000327.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000009.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000009.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000009
