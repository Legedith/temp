function handleIt() {
                var email = document.getElementById("email");
                var username = document.getElementById("username");
                var password = document.getElementById("pwd");
                var confirm_password = document.getElementById("pwd");
                // Max length of email is 60
                var r = "";
                if (email.value == "" || username.value == "" || password.value == "" || confirm_password.value == "") {
                        r = "Please fill out all fields: \n Email \n Username \n Password \n Confirm Password \n";
                }

                // Password exact length is 8
                if (password.value.length < 8) {
                    r += "Password length should be atleast 8 characters\n";
                    
                }
                //password should have a number
                if (password.value.search(/[0-9]/) == -1) {
                    r += "Password should have atleast one number\n";
                }


                // Password should contain a special character from @, $, !, &, etc.
                if (password.value.match(/[@$!%*#?&]/) == null) {
                    r += "Password should contain a special character from @, $, !, &, etc.\n";
                }
                // First letter of password must be capital
                if (password.value.match(/^[A-Z]/) == null) {
                    r += "First letter of password must be capital\n";
                }
                // No two consecutive letters in password should be same
                if (password.value.match(/(.)\1/) != null) {
                    r += "No two consecutive letters in password should be same\n";
                }

                // Password and confirm password should be same
                if (password.value != confirm_password.value) {
                    r += "Password and confirm password should be same\n";
                    
                }
                // create alert if r
                if (r != "") {
                    alert(r);
                }
                else{
                    // Open google scholar with placeholder text in searchbox username
                    window.open("https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=" + username.value);
                }
            }