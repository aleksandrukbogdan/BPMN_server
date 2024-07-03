datapost = 
async function FetchPost(datapost){
    console.log(JSON.stringify(datapost))
    try {
        const response = await fetch('http://127.0.0.1:3000/api/',{
          method:  'POST',
          headers: {
            'Content-Type': 'application/bpmn'
          },
          body: JSON.stringify(datapost)
        })
        if (!response.ok) {
            throw new Error('Network response was not ok');
        }
        else{
            return await response.json();
        }
        } catch (error) {
            console.log('Error save:', error);
            return error;
            
        }
}